use std::{cell::{Ref, RefCell}, collections::HashMap, mem, rc::Rc};

use indexmap::IndexMap;
use logos::Span;
use slotmap::{new_key_type, SlotMap};
use smol_str::SmolStr;
use thiserror::Error;

use crate::{ast::{Callback, Method, MethodTy, Node, NodeValue, Reference, SpanNode, Type}, resolve};

#[derive(Error, Debug)]
pub enum EvalError {
    #[error("type mismatch: expected type `{expected}` got `{got}`")]
    TypeMismatch { expected: String, got: Type, span: Span },
    #[error("expected additional field")]
    ExpectedAdditionalField { span: Span },
    #[error("got unexpected field `{got}` when creating struct instance")]
    UnexpectedField { got: String, span: Span },
    #[error("could not find method match")]
    NoMethodMatches { span: Span },
    #[error("attempted to call non-func as func")]
    CalledNonFunc { span: Span },
    #[error("attempted to dereference undefined variable `{name}`")]
    UndefinedVar { name: String, span: Span },
    #[error("error")]
    Generic(Span)
}
impl EvalError {
    pub fn span(&self) -> Span {
        match self {
            Self::TypeMismatch { span, .. } |
            Self::ExpectedAdditionalField { span, .. } |
            Self::UnexpectedField { span, .. } |
            Self::NoMethodMatches { span, .. } |
            Self::CalledNonFunc { span, .. } |
            Self::UndefinedVar { span, .. } |
            Self::Generic(span) => span.clone()
        }
    }
}

new_key_type! { pub struct EnvironmentKey; }
#[derive(Default, Debug, PartialEq)]
pub struct EnvironmentScope {
    pub bindings: HashMap<SmolStr, SpanNode>,
    up: Option<EnvironmentKey>,
}
#[derive(Default, Debug)]
pub struct Environment {
    pub global: EnvironmentKey,
    scopes: SlotMap<EnvironmentKey, EnvironmentScope>
}
impl Environment {
    pub fn new() -> Self {
        let global_scope = EnvironmentScope {
            ..Default::default()
        };
        let mut scopes = SlotMap::<EnvironmentKey, EnvironmentScope>::with_key();
        let global_scope_key = scopes.insert(global_scope);
        Self { global: global_scope_key, scopes, ..Default::default() }
    }

    pub fn new_child(&mut self, current: EnvironmentKey) -> EnvironmentKey {
        let child_scope = EnvironmentScope {
            up: Some(current),
            ..Default::default()
        };
        self.scopes.insert(child_scope)
    }

    pub fn get_scope(&self, current: EnvironmentKey) -> Option<&EnvironmentScope> {
        self.scopes.get(current)
    }

    pub fn get(&self, current: EnvironmentKey, name: &SmolStr) -> Option<&SpanNode> {
        if let Some(binding) = self.scopes.get(current).unwrap().bindings.get(name) {
            return Some(binding);
        }

        let mut current = current;
        while let Some(parent) = self.scopes.get(current).unwrap().up {
            current = parent;
            if let Some(binding) = self.scopes.get(current).unwrap().bindings.get(name) {
                return Some(binding);
            }
        }

        None
    }
    pub fn has(&self, current: EnvironmentKey, name: &SmolStr) -> bool {
        self.get(current, name).is_some()
    }
    pub fn set(&mut self, current: EnvironmentKey, name: SmolStr, value: SpanNode, shadow: bool) {
        if self.has(current, &name) && !shadow {
            if let Some(binding) = self.scopes.get_mut(current).unwrap().bindings.get_mut(&name) {
                let _ = mem::replace(binding, value);
                return;
            }

            let mut current = current;
            while let Some(parent) = self.scopes.get(current).unwrap().up {
                current = parent;
                if let Some(binding) = self.scopes.get_mut(current).unwrap().bindings.get_mut(&name) {
                    let _ = mem::replace(binding, value);
                    return;
                }
            }
        } else {
            self.scopes.get_mut(current).unwrap().bindings.insert(name, value);
        }
    }
    pub fn def(&mut self, current: EnvironmentKey, name: SmolStr, value: SpanNode) {
        if self.has(current, &name) {
            let (ty, list) = self.get(current, &name).unwrap().clone().with_type();
            assert!(ty.is_function());
            list.into_list().unwrap().borrow_mut().push(value);
        } else {
            self.set(
                current,
                name, 
                Node::new_typed(Default::default(), Type::Function,
                    Node::new_list(Default::default(), Reference::new(vec![value]))
                ), false
            );
        }
    }

    pub fn global_get(&mut self, name: &SmolStr) -> Option<&SpanNode> {
        self.get(self.global, name)
    }
    pub fn global_set(&mut self, name: SmolStr, value: SpanNode) {
        self.set(self.global, name, value, false)
    }
    pub fn global_def(&mut self, name: SmolStr, value: SpanNode) {
        self.def(self.global, name, value)
    }

    pub fn def_rust_method(&mut self, current: EnvironmentKey, name: SmolStr, value: Box<Callback>, ty: Type) {
        self.def(current, name, Node::new_method(Default::default(), Reference::new(
            Method::Rust { callback: value, ty }
        )))
    }
    pub fn def_rust_macro(&mut self, current: EnvironmentKey, name: SmolStr, value: Box<Callback>) {
        self.def_rust_method(current, name, value, Type::Macro);
    }
    pub fn def_special_form(&mut self, current: EnvironmentKey, name: SmolStr, value: Box<Callback>) {
        self.def_rust_method(current, name, value, Type::SpecialForm);
    }

    pub fn global_def_rust_method(&mut self, name: SmolStr, value: Box<Callback>, ty: MethodTy) {
        self.def_rust_method(self.global, name, value, Type::Method(ty, 0));
    }
    pub fn global_def_rust_macro(&mut self, name: SmolStr, value: Box<Callback>) {
        self.def_rust_macro(self.global, name, value);
    }
    pub fn global_def_special_form(&mut self, name: SmolStr, value: Box<Callback>) {
        self.def_special_form(self.global, name, value);
    }
}

pub fn eval_call(
    func_symbol: SpanNode,
    func: SpanNode,
    mut args: impl Iterator<Item = SpanNode>,
    env: &mut Environment,
    env_key: EnvironmentKey
) -> Result<SpanNode, EvalError> {
    if func.ty().is_function() {
        /*let methods = func.with_type().1.into_list().unwrap();
        let methods: Vec<Reference<Method>> = methods.borrow().iter().cloned().map(|m| m.into_method().unwrap()).collect();
        
        let is_special_form = methods.first().map(|m| matches!(*m.borrow(), Method::Rust { ty: Type::SpecialForm, .. })).unwrap_or_default();
        let is_macro = methods.first().map(|m| matches!(*m.borrow(), Method::Rust { ty: Type::Macro, .. })).unwrap_or_default();
        let (call_tys, call_args): (Vec<_>, Vec<_>) =
            args.map(|arg| {
                if is_special_form || is_macro {
                    Ok((arg.ty(), arg))
                } else {
                    let evaled = eval(arg, env, env_key)?;
                    Ok::<_, EvalError>((evaled.ty(), evaled))
                }
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter().unzip();*/

        let (is_special_form, is_macro) = {
            let (_, methods) = func.as_typed().unwrap();
            let methods: Vec<Reference<Method>> = methods.as_list().unwrap().borrow().iter().cloned().map(|m| m.as_method().unwrap().cloned()).collect();
            
            let is_special_form = methods.first().map(|m| matches!(*m.borrow(), Method::Rust { ty: Type::SpecialForm, .. })).unwrap_or_default();
            let is_macro = methods.first().map(|m| matches!(*m.borrow(), Method::Rust { ty: Type::Macro, .. })).unwrap_or_default();

            (is_special_form, is_macro)
        };
        let (call_tys, call_args): (Vec<_>, Vec<_>) =
            args.map(|arg| {
                if is_special_form || is_macro {
                    Ok((arg.ty(), arg))
                } else {
                    let evaled = eval(arg, env, env_key)?;
                    Ok::<_, EvalError>((evaled.ty(), evaled))
                }
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter().unzip();

        let get_methods = |func: &str| -> Vec<(Type, Reference<Method>)> {
            if let Some((ty, methods)) = env.get(env_key, &func.into()).cloned().map(|x| x.with_type()) {
                if ty.is_function() {
                    let methods = methods.as_list().unwrap().borrow();
                    return methods.iter().map(|x| (x.ty(), x.as_method().unwrap().cloned())).collect();
                }
            }
            Vec::new()
        };

        let (method, method_ret_ty) = if is_special_form || is_macro {
            let (_, methods) = func.as_typed().unwrap();
            let (method, method_ty) = methods.as_list().unwrap().borrow().iter().cloned()
                         .map(|m| (m.as_method().unwrap().cloned(), m.ty())).next().unwrap();
            (method, Type::Unknown)
        } else {
            let resolved = resolve::resolve_method(&func_symbol, call_tys, get_methods)?;
            (resolved.data.expect("Encountered abstract function resolution at eval time"), resolved.ret_ty)
        };

        match &*method.borrow() {
            Method::Hop { param_names, def_env_key, body, ty } => {
                let method_ty = ty.as_method().unwrap();
                // Call method
                // Create a new scope
                let new_env_key = env.new_child(*def_env_key);

                for (param, arg) in param_names.into_iter().zip(call_args.into_iter()) {
                    //println!("Setting function env {param} = {arg}");
                    env.set(new_env_key, param.clone(), arg, true);
                }

                let res = eval(*body.clone(), env, new_env_key)?;
                let res_ty = res.ty();
                return if method_ret_ty.compatible(&res_ty) {
                    Ok(res)
                } else {
                    Err(EvalError::TypeMismatch { expected: format!("{}", method_ret_ty), got: res_ty, span: body.tag.clone() })
                };
            },
            Method::Rust { callback, ty } => {
                return callback(
                    call_args.into_iter(),
                    env,
                    env_key
                );
            }
        }

        //println!("Searching for method match!");
        /*for method in methods {
            let borrowed = method.borrow();
            match &*borrowed {
                Method::Hop { param_names, env: env_key, body, ty } => {
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
                            if a.compatible(b, &mut placeholder_matches) {
                                true
                            } else {
                                //println!("    - {a} not compatible with {b}");
                                false
                            }
                        }).count() == param_count
                    {
                        // Call method
                        // Create a new scope
                        let mut new_env_key = env.new_child(*env_key);

                        for (param, arg) in method_param_names.into_iter().zip(call_args.into_iter()) {
                            //println!("Setting function env {param} = {arg}");
                            env.set(new_env_key, param.clone(), arg, true);
                        }

                        let res = eval(*body.clone(), env, new_env_key)?;
                        let res_ty = res.ty();
                        return if method_ret_ty.compatible(&res_ty, &mut placeholder_matches) {
                            Ok(res)
                        } else {
                            Err(EvalError::TypeMismatch { expected: format!("{}", method_ret_ty), got: res_ty, span: body_tag })
                        };
                    }
                },
                Method::Rust { callback, ty } => {
                    if *ty == Type::SpecialForm { return callback(call_args.into_iter(), env, env_key) } // Macro
                    if *ty == Type::Macro { return eval(callback(call_args.into_iter(), env, env_key)?, env, env_key) } // Macro
                    let method_ty = ty.clone().into_method().unwrap();
                    let method_param_tys = method_ty.0;
                    let method_ret_ty = method_ty.1;
                    let param_count = method_param_tys.len();

                    if param_count != call_tys.len() { continue; }

                    // Method match
                    let mut placeholder_matches: HashMap<SmolStr, Type> = HashMap::new();
                    if method_param_tys.iter().zip(&call_tys)
                        .filter(|&(a, b)| {
                            if a.compatible(b,  &mut placeholder_matches) {
                                true
                            } else {
                                //println!("    - {a} not compatible with {b}");
                                false
                            }
                        }).count() == param_count
                    {
                        return callback(
                            call_args.into_iter(),
                            env,
                            env_key
                        );
                    }
                }
            }
        }*/
        return Err(EvalError::NoMethodMatches { span: func_symbol.tag });
    } else if let NodeValue::Type(ty) = func.node {
        // Create type instance
        match ty {
            Type::Struct(_) => {
                let val = eval(args.next().unwrap(), env, env_key)?;
                // FIXME: Check that fields are correct
                Ok(Node::new_typed(func.tag, ty, val))
            },
            Type::Enum(ref variants) => {
                let variants = variants.as_table().unwrap().borrow();
                let enum_tag = args.next().unwrap();
                assert!(enum_tag.is_keyword());
                let variant = variants.get(&enum_tag).unwrap().as_type().unwrap();
                let value = args.next().unwrap_or_else(|| todo!());

                let create_variant_list = SpanNode::new_list(Default::default(), Reference::new(
                    vec![Node::new_type(Default::default(), variant.clone()), value.clone()]
                ));
                let got = eval(create_variant_list, env, env_key)?;
                let got_ty = got.ty();
                let expected_ty = variant;
                if got_ty != *expected_ty {
                    return Err(EvalError::TypeMismatch { expected: format!("{expected_ty}"), got: got_ty, span: func.tag })
                }
                Ok(Node::new_typed(func.tag.clone(), ty.clone(),
                    Node::new_table(func.tag, Reference::new(IndexMap::from([
                        (Node::new_symbol(Default::default(), "tag".into()), enum_tag.clone()),
                        (Node::new_symbol(Default::default(), "value".into()), got),
                    ])))
                ))
            },
            Type::String => {
                Ok(args.next().unwrap())
            },
            Type::TypeVariable { id, implements } => {
                assert!(implements.is_none());
                let imp_list: Vec<SpanNode> = args.map(|arg| eval(arg, env, env_key)).collect::<Result<_, _>>()?;
                for imp in &imp_list {
                    assert!(imp.is_implementation());
                }
                Ok(SpanNode::new_type(func.tag, Type::TypeVariable {
                    id,
                    implements: Some(imp_list.into_iter().map(|i| i.into_implementation().unwrap()).collect())
                }))
            },
            _ => todo!()
        }
    } else {
        return Err(EvalError::CalledNonFunc { span: func_symbol.tag });
    }
}
pub fn eval(
    node: SpanNode,
    env: &mut Environment,
    env_key: EnvironmentKey
) -> Result<SpanNode, EvalError> {
    match node.node {
        NodeValue::Bool(_) | NodeValue::Number(_) | NodeValue::String(_) | NodeValue::Keyword(_) | NodeValue::Type(_) | NodeValue::Typed(_, _) => Ok(node),
        NodeValue::Symbol(name) => {
            Ok(env.get(env_key, &name).ok_or(EvalError::UndefinedVar { name: name.to_string(), span: node.tag })?.clone())
        },
        NodeValue::List(ref list) => {
            if list.borrow().len() == 0 {
                Ok(node)
            } else {
                let list = list.borrow();
                let func_symbol = list.first().cloned().unwrap();
                let func = eval(func_symbol.clone(), env, env_key)?;
                let args = list.iter().cloned().skip(1);
                eval_call(func_symbol, func, args, env, env_key)
            }
        },
        NodeValue::Table(ref table) => {
            let mut new_table: IndexMap<SpanNode, SpanNode> = IndexMap::new();
            {
                let table = table.borrow();
                for (k, v) in table.iter() {
                    new_table.insert(eval(k.clone(), env, env_key)?, eval(v.clone(), env, env_key)?);
                }
            }
            Ok(Node::new_table(node.tag, Reference::new(new_table)))
        },
        _ => todo!("{node}")
    }
}