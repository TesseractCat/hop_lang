use std::{cell::RefCell, collections::HashMap, mem, rc::Rc};

use logos::Span;
use smol_str::SmolStr;
use thiserror::Error;

use crate::ast::{Callback, Method, Node, NodeValue, Reference, SpanNode, Type};

#[derive(Error, Debug)]
pub enum EvalError {
    #[error("type mismatch: expected type {expected} got {got}")]
    TypeMismatch { expected: String, got: Type, span: Span },
    #[error("could not find method match")]
    NoMethodMatches { span: Span },
    #[error("attempted to call non-func as func")]
    CalledNonFunc { span: Span },
    #[error("attempted to dereference undefined variable")]
    UndefinedVar { span: Span },
    #[error("error")]
    Generic(Span)
}
impl EvalError {
    pub fn span(&self) -> Span {
        match self {
            Self::TypeMismatch { span, .. } |
            Self::NoMethodMatches { span, .. } |
            Self::CalledNonFunc { span, .. } |
            Self::UndefinedVar { span, .. } |
            Self::Generic(span) => span.clone()
        }
    }
}

#[derive(Default, Debug, PartialEq)]
pub struct Environment {
    bindings: HashMap<SmolStr, SpanNode>,
    up: Option<Rc<RefCell<Self>>>,
    global: Option<Rc<RefCell<Self>>>
}
impl Environment {
    pub fn new_child(this: Rc<RefCell<Self>>) -> Self {
        Self {
            up: Some(Rc::clone(&this)),
            global: Some(
                if this.borrow().global.is_some() {
                    this.borrow().global.clone().unwrap()
                } else {
                    this
                }
            ),
            ..Default::default()
        }
    }

    pub fn get(&self, name: &SmolStr) -> Option<SpanNode> {
        if let Some(binding) = self.bindings.get(name) {
            Some(binding.clone())
        } else if let Some(up) = self.up.as_ref().map(|r| Rc::clone(&r)) {
            let mut env = up;
            while env.borrow().bindings.get(name).is_none() {
                let up = env.borrow().up.as_ref().map(|r| Rc::clone(&r));
                if let Some(up) = up {
                    env = up;
                } else {
                    break;
                }
            }
            let r = env.borrow().bindings.get(name).cloned();
            r
        } else {
            None
        }
    }
    pub fn has(&self, name: &SmolStr) -> bool {
        self.get(name).is_some()
    }
    pub fn set(&mut self, name: SmolStr, value: SpanNode, shadow: bool) {
        if self.has(&name) && !shadow {
            if let Some(binding) = self.bindings.get_mut(&name) {
                let _ = mem::replace(binding, value);
            } else if let Some(up) = self.up.as_ref().map(|r| Rc::clone(&r)) {
                let mut env = up;
                while env.borrow().bindings.get(&name).is_none() {
                    let up = env.borrow().up.as_ref().map(|r| Rc::clone(&r));
                    if let Some(up) = up {
                        env = up;
                    } else {
                        break;
                    }
                }
                let mut borrow = env.borrow_mut();
                let binding = borrow.bindings.get_mut(&name);
                if let Some(binding) = binding {
                    let _ = mem::replace(binding, value);
                }
            }
        } else {
            self.bindings.insert(name, value.clone());
        }
    }
    pub fn def(&mut self, name: SmolStr, value: SpanNode) {
        if self.has(&name) {
            let (ty, list) = self.get(&name).unwrap().with_type();
            assert!(ty.is_function());
            list.into_list().unwrap().borrow_mut().push(value);
        } else {
            self.set(
                name.clone(), 
                Node::new_typed(Default::default(), Type::Function,
                    Node::new_list(Default::default(), Reference::new(vec![value]))
                ), false
            );
        }
    }

    pub fn global_get(&mut self, name: &SmolStr) -> Option<SpanNode> {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().get(name)
        } else {
            self.get(name)
        }
    }
    pub fn global_set(&mut self, name: SmolStr, value: SpanNode) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().set(name, value, false);
        } else {
            self.set(name, value, false);
        }
    }
    pub fn global_def(&mut self, name: SmolStr, value: SpanNode) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().def(name, value);
        } else {
            self.def(name, value);
        }
    }

    pub fn def_rust_method(&mut self, name: SmolStr, value: Box<Callback>, ty: Type) {
        self.def(name, Node::new_method(Default::default(), Reference::new(
            Method::Rust { callback: value, ty }
        )))
    }
    pub fn def_rust_macro(&mut self, name: SmolStr, value: Box<Callback>) {
        self.def_rust_method(name, value, Type::Unknown);
    }
}

pub fn eval_call(func_symbol: SpanNode, func: SpanNode, mut args: impl Iterator<Item = SpanNode>, env: &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError> {
    if func.ty().is_function() {
        let methods = func.with_type().1.into_list().unwrap();
        let methods: Vec<Reference<Method>> = methods.borrow().iter().cloned().map(|m| m.into_method().unwrap()).collect();
        
        let is_macro = methods.first().map(|m| matches!(*m.borrow(), Method::Rust { ty: Type::Unknown, .. })).unwrap_or_default();
        let (call_tys, call_args): (Vec<_>, Vec<_>) =
            args.map(|arg| {
                if is_macro {
                    Ok((arg.ty(), arg))
                } else {
                    let evaled = eval(arg, env)?;
                    Ok::<_, EvalError>((evaled.ty(), evaled))
                }
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter().unzip();

        //println!("Searching for method match!");
        for method in methods {
            let borrowed = method.borrow();
            match &*borrowed {
                Method::Hop { param_names, env, body, ty } => {
                    let method_ty = ty.clone().into_method().unwrap();
                    let method_param_names = param_names;
                    let method_param_tys = method_ty.0;
                    let method_ret_ty = method_ty.1;
                    let param_count = method_param_tys.len();
                    let body_tag = body.tag.clone();

                    if param_count != call_tys.len() { continue; }

                    //println!(" - {:?} vs. {:?}", call_tys, method_param_tys);

                    // Method match
                    let mut placeholder_matches: HashMap<SmolStr, Type> = HashMap::new();
                    if method_param_tys.iter().zip(&call_tys)
                        .filter(|&(a, b)| {
                            if a.compatible(b, &*env.borrow(), &mut placeholder_matches) {
                                true
                            } else {
                                //println!("    - {a} not compatible with {b}");
                                false
                            }
                        }).count() == param_count
                    {
                        // Call method
                        // Create a new scope
                        let mut new_env = Environment::new_child(Rc::clone(env));

                        for (param, arg) in method_param_names.into_iter().zip(call_args.into_iter()) {
                            //println!("Setting function env {param} = {arg}");
                            new_env.set(param.clone(), arg, true);
                        }

                        let new_env_rc = Rc::new(RefCell::new(new_env));
                        let res = eval(*body.clone(), &new_env_rc)?;
                        let res_ty = res.ty();
                        return if method_ret_ty.compatible(&res_ty, &*env.borrow(), &mut placeholder_matches) {
                            Ok(res)
                        } else {
                            Err(EvalError::TypeMismatch { expected: format!("{}", method_ret_ty), got: res_ty, span: body_tag })
                        };
                    }
                },
                Method::Rust { callback, ty } => {
                    if *ty == Type::Unknown { return callback(call_args.into_iter(), env) } // Macro
                    let method_ty = ty.clone().into_method().unwrap();
                    let method_param_tys = method_ty.0;
                    let method_ret_ty = method_ty.1;
                    let param_count = method_param_tys.len();

                    if param_count != call_tys.len() { continue; }

                    // Method match
                    let mut placeholder_matches: HashMap<SmolStr, Type> = HashMap::new();
                    if method_param_tys.iter().zip(&call_tys)
                        .filter(|&(a, b)| {
                            if a.compatible(b, &*env.borrow(), &mut placeholder_matches) {
                                true
                            } else {
                                //println!("    - {a} not compatible with {b}");
                                false
                            }
                        }).count() == param_count
                    {
                        return callback(
                            call_args.into_iter()
                                .map(|arg| eval(arg, env))
                                .collect::<Result<Vec<_>, _>>()?.into_iter(),
                            env
                        );
                    }
                }
            }
        }
        return Err(EvalError::NoMethodMatches { span: func_symbol.tag });
    } else if let NodeValue::Type(ty) = func.node {
        // Create type instance
        let val = eval(args.next().unwrap(), env)?;
        Ok(Node::new_typed(func.tag, ty, val))
    } else {
        return Err(EvalError::CalledNonFunc { span: func_symbol.tag });
    }
}
pub fn eval(node: SpanNode, env: &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError> {
    match node.node {
        NodeValue::Bool(_) | NodeValue::Number(_) | NodeValue::String(_) | NodeValue::Type(_) | NodeValue::Typed(_, _) => Ok(node),
        NodeValue::Symbol(name) => {
            Ok(env.borrow_mut().get(&name).ok_or(EvalError::UndefinedVar { span: node.tag })?.clone())
        },
        NodeValue::List(list) => {
            if list.borrow().len() == 0 {
                Ok(Node::new_list(node.tag, list))
            } else {
                let list = list.borrow();
                let func_symbol = list.first().cloned().unwrap();
                let func = eval(func_symbol.clone(), env)?;
                let args = list.iter().cloned().skip(1);
                eval_call(func_symbol, func, args, env)
            }
        },
        NodeValue::Table(table) => {
            {
                let mut table = table.borrow_mut();
                table.values_mut().map(|val| {
                    let _ = mem::replace(val, eval(val.clone(), env)?);
                    Ok::<_, EvalError>(())
                }).collect::<Result<(), _>>()?;
            }
            Ok(Node::new_table(node.tag, table))
        },
        _ => todo!("{node}")
    }
}