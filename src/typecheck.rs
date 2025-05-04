use std::{collections::HashMap, mem};

use slotmap::{new_key_type, SlotMap};
use smol_str::SmolStr;

use crate::{
    ast::{MethodTy, Node, NodeValue, Reference, SpanNode, Type},
    eval::{Environment, EnvironmentKey, EvalError},
    get_new_method_id,
    resolve
};

new_key_type! { pub struct TypeEnvironmentKey; }
#[derive(Default, Debug, PartialEq)]
pub struct TypeEnvironmentScope {
    static_env_key: EnvironmentKey,
    bindings: HashMap<SmolStr, Type>,
    functions: HashMap<SmolStr, Vec<Type>>,
    up: Option<TypeEnvironmentKey>,
}

#[derive(Default, Debug)]
pub struct TypeEnvironment {
    pub global: TypeEnvironmentKey,
    static_env: Environment,
    scopes: SlotMap<TypeEnvironmentKey, TypeEnvironmentScope>
}
impl TypeEnvironment {
    pub fn new() -> Self {
        let static_env = Environment::new();
        let global_scope = TypeEnvironmentScope {
            static_env_key: static_env.global,
            ..Default::default()
        };
        let mut scopes = SlotMap::<TypeEnvironmentKey, TypeEnvironmentScope>::with_key();
        let global_scope_key = scopes.insert(global_scope);
        Self { global: global_scope_key, static_env, scopes }
    }

    pub fn new_child(&mut self, current: TypeEnvironmentKey) -> TypeEnvironmentKey {
        let child_static_env_key = self.static_env.new_child(self.scopes[current].static_env_key);
        let child_scope = TypeEnvironmentScope {
            static_env_key: child_static_env_key,
            up: Some(current),
            ..Default::default()
        };
        self.scopes.insert(child_scope)
    }

    pub fn get(&self, current: TypeEnvironmentKey, name: &SmolStr) -> Option<&Type> {
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
    pub fn get_function(&self, current: TypeEnvironmentKey, name: &SmolStr) -> Option<&[Type]> {
        if let Some(binding) = self.scopes.get(current).unwrap().functions.get(name) {
            return Some(binding);
        }

        let mut current = current;
        while let Some(parent) = self.scopes.get(current).unwrap().up {
            current = parent;
            if let Some(binding) = self.scopes.get(current).unwrap().functions.get(name) {
                return Some(binding);
            }
        }

        None
    }
    pub fn has(&self, current: TypeEnvironmentKey, name: &SmolStr) -> bool {
        self.get(current, name).is_some()
    }
    pub fn set(&mut self, current: TypeEnvironmentKey, name: SmolStr, value: Type, shadow: bool) {
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
    pub fn def(&mut self, current: TypeEnvironmentKey, name: SmolStr, value: Type) {
        if self.scopes[current].functions.contains_key(&name) {
            self.scopes[current].functions.get_mut(&name).unwrap().push(value);
        } else {
            self.scopes[current].functions.insert(name, vec![value]);
        }
    }

    /*pub fn global_get(&mut self, current: TypeEnvironmentKey, name: &SmolStr) -> Option<&Type> {
        if let Some(v) = self.scopes[self.global].bindings.get(name) {
            Some(v)
        } else {
            self.get(current, name)
        }
    }
    pub fn global_set(&mut self, name: SmolStr, value: Type) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().set(name, value, false);
        } else {
            self.set(name, value, false);
        }
    }
    pub fn global_def(&mut self, name: SmolStr, value: Type) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().def(name, value);
        } else {
            self.def(name, value);
        }
    }*/
}

pub fn typecheck_call(
    func_symbol: &SpanNode,
    args: impl Iterator<Item = Type>,
    env: &TypeEnvironment,
    env_key: TypeEnvironmentKey
) -> Result<Type, EvalError> {
    let get_methods_by_name = |name: &str| -> Vec<(Type, ())> {
        env.get_function(env_key, &name.into()).unwrap_or(&[])
            .into_iter().cloned().map(|x| (x, ())).collect()
    };
    let call_tys = args.collect::<Vec<_>>();
    resolve::resolve_method(func_symbol, call_tys, get_methods_by_name)
        .map(|x| x.ret_ty)
}

pub fn typecheck(
    node: &SpanNode,
    env: &mut TypeEnvironment,
    env_key: TypeEnvironmentKey
) -> Result<Type, EvalError> {
    match &node.node {
        NodeValue::Bool(_) => Ok(Type::Bool),
        NodeValue::Number(_) => Ok(Type::Number),
        NodeValue::String(_) => Ok(Type::String),
        NodeValue::Symbol(name) => {
            Ok(env.get(env_key, &name).ok_or(EvalError::UndefinedVar { name: name.to_string(), span: node.tag.clone() })?.clone())
        },
        NodeValue::Typed(ty, _) => Ok(ty.clone()),
        NodeValue::Type(ty) => Ok(Type::Type(Some(Box::new(ty.clone())))),
        NodeValue::List(list) => {
            let list = list.borrow();
            if list.len() == 0 { return Ok(Type::UntypedList); }
            let mut list = list.iter();
            let first = list.next().unwrap();
            let builtin = first.node.as_symbol().map(|s| s.as_str());
            
            match builtin {
                Some("do") => {
                    let mut last = Type::Unit;
                    let new_env_key = env.new_child(env_key);
                    while let Some(elem) = list.next() {
                        last = typecheck(elem, env, new_env_key)?;
                    }
                    Ok(last)
                },
                Some("let") => {
                    let symbol_node = list.next()
                        .ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let symbol = symbol_node.node.as_symbol()
                        .ok_or(EvalError::TypeMismatch { expected: "Symbol".into(), got: symbol_node.ty(), span: symbol_node.tag.clone() })?;
                    let val = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let val_ty = typecheck(val, env, env_key)?;
                    env.set(env_key, symbol.clone(), val_ty, true);
                    Ok(Type::UntypedList)
                },
                Some("set") => {
                    let symbol_node = list.next()
                        .ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let symbol = symbol_node.node.as_symbol()
                        .ok_or(EvalError::TypeMismatch { expected: "Symbol".into(), got: symbol_node.ty(), span: symbol_node.tag.clone() })?;
                    let val = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    // FIXME: Probably don't need the clone here
                    if let Some(to_ty) = env.get(env_key, symbol).cloned() {
                        let from_ty = typecheck(val, env, env_key)?;
                        if from_ty != to_ty {
                            Err(EvalError::TypeMismatch { expected: format!("{}", to_ty), got: from_ty, span: val.tag.clone() })
                        } else {
                            Ok(Type::UntypedList)
                        }
                    } else {
                        Err(EvalError::UndefinedVar { name: symbol.to_string(), span: symbol_node.tag.clone() })
                    }
                },
                Some("struct") => {
                    let table = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    // Ok(Type::Type(Box::new(
                    //     Type::Struct(Box::new(table.clone()))
                    // )))
                    Ok(Type::Type(None))
                },
                Some("fn") => {
                    let params = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let arrow = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let ret = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let ret = ret.clone();

                    let param_names: Vec<SmolStr> = params.as_table().unwrap().borrow()
                        .keys().cloned().map(|n| n.into_keyword().unwrap()).collect();
                    let param_tys: Vec<Type> = params.as_table().unwrap().borrow().values().map(|v| v.as_type().unwrap().clone()).collect();
                    let ret_ty = ret.into_type().map_err(|e| EvalError::TypeMismatch { expected: "Type".into(), got: e.ty(), span: e.tag })?;

                    let method_ty = Type::Method(MethodTy {
                        params: param_tys, ret: Box::new(ret_ty)
                    }, get_new_method_id());
                    let mut type_variable_impls = HashMap::new();

                    // Recurse typecheck function body
                    {
                        let flattened_method_ty = resolve::flatten_impls(
                            resolve::rename_tv_names(method_ty.clone()),
                            &mut type_variable_impls
                        );

                        let method_ty = flattened_method_ty.as_method().unwrap().0;
                        let new_env_key = env.new_child(env_key);
                        for (param_name, param_ty) in param_names.iter().zip(method_ty.params.iter()) {
                            //println!("Setting function env {param_name} = {param_ty}");
                            let param_ty = match param_ty {
                                Type::TypeVariable { id, .. } => Type::TypeVariable {
                                    id: id.clone(),
                                    implements: type_variable_impls.get(id).cloned().map(|x| x.into_iter().collect())
                                },
                                x => x.clone()
                            };
                            env.set(new_env_key, param_name.clone(), param_ty, true);
                        }
    
                        let body = list.next().unwrap();
                        let body_ty = typecheck(body, env, new_env_key)?;

                        let ret_ty = match &*method_ty.ret {
                            Type::TypeVariable { id, .. } => &Type::TypeVariable {
                                id: id.clone(),
                                implements: type_variable_impls.get(id).cloned().map(|x| x.into_iter().collect())
                            },
                            x => x
                        };

                        if !ret_ty.compatible(&body_ty, false) {
                            return Err(EvalError::TypeMismatch { expected: format!("{}", ret_ty), got: body_ty, span: body.tag.clone() });
                        }
                    }

                    Ok(method_ty)
                },
                Some("def") => {
                    let func = list.next().unwrap();
                    let method = list.next().unwrap();

                    let method_ty = typecheck(method, env, env_key)?;
                    let func_name = func.as_symbol().unwrap();

                    env.def(env_key, func_name.clone(), method_ty);

                    Ok(Type::UntypedList)
                },
                Some("print") => {
                    let val = list.next().unwrap();
                    typecheck(val, env, env_key)
                },
                Some("call") => {
                    unimplemented!()
                },
                Some(func) => {
                    typecheck_call(
                        first,
                        list.map(|e| typecheck(e, env, env_key)).collect::<Result<Vec<_>,_>>()?.into_iter(),
                        env,
                        env_key
                    )
                },
                _ => {
                    let first_tag = first.tag.clone();
                    let first = typecheck(first, env, env_key)?;
                    if let Type::Type(Some(ty)) = first {
                        match &*ty {
                            Type::Struct(fields) => {
                                let fields = fields.as_table().unwrap().borrow();
                                let table = list.next().unwrap().as_table().unwrap();
                                for (k, v) in table.borrow().iter() {
                                    let v_ty = typecheck(v, env, env_key)?;

                                    if let Some(expected_ty) = fields.get(k) {
                                        let expected_ty = expected_ty.as_type().unwrap();
                                        if &v_ty != expected_ty {
                                            return Err(EvalError::TypeMismatch { expected: format!("{}", expected_ty), got: v_ty, span: v.tag.clone() });
                                        }
                                    } else {
                                        return Err(EvalError::UnexpectedField { got: k.to_string(), span: v.tag.clone() });
                                    }
                                }
                                Ok(*ty.clone())
                            },
                            Type::Enum(variants) => {
                                let variants = variants.as_table().unwrap().borrow();
                                let enum_tag = list.next().unwrap();
                                assert!(enum_tag.is_keyword());
                                println!("getting {enum_tag:?} from {variants:?}");
                                let variant = variants.get(enum_tag).expect("Invalid variant").as_type().unwrap();
                                let unit_ty = Node::new_type(Default::default(), Type::Unit);
                                let value = list.next().unwrap_or(&unit_ty);

                                let create_variant_list = SpanNode::new_list(Default::default(), Reference::new(
                                    vec![Node::new_type(Default::default(), variant.clone()), value.clone()]
                                ));
                                let got_ty = typecheck(&create_variant_list, env, env_key)?;
                                let expected_ty = variant;
                                if got_ty != *expected_ty {
                                    return Err(EvalError::TypeMismatch { expected: format!("{expected_ty}"), got: got_ty, span: first_tag })
                                }
                                Ok(*ty.clone())
                            },
                            Type::String => Ok(Type::String),
                            _ => todo!("{ty}")
                        }
                    } else {
                        todo!("{first}")
                    }
                }
            }
        },
        NodeValue::Table(_) => Ok(Type::UntypedTable),
        _ => todo!("{node}")
    }
}