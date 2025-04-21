use codespan_reporting::{diagnostic::{Diagnostic, Label}, files::SimpleFiles, term::termcolor::{ColorChoice, StandardStream}};
use eval::{Environment, EnvironmentKey, EvalError};
use indexmap::IndexMap;
use logos::Logos;
use slotmap::{new_key_type, SlotMap};
use smol_str::SmolStr;
use std::{cell::RefCell, collections::HashMap, env, fs, hash::Hash, io::BufWriter, mem, rc::Rc};

mod tokenize;
use tokenize::{parse_block, Token};
mod ast;
use ast::{Implementation, Method, Node, NodeValue, Reference, SpanNode, Type};
mod eval;
use eval::{eval, eval_call};
mod resolve;

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
    let get_methods_by_name = |name: &str| -> Option<&[Type]> {
        env.get_function(env_key, &name.into())
    };
    resolve::resolve_method(func_symbol, args, get_methods_by_name)
}

fn typecheck(
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
                    let mut last = Type::UntypedList;
                    while let Some(elem) = list.next() {
                        last = typecheck(elem, env, env_key)?;
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

                    // Recurse typecheck function body
                    let mut new_env_key = env.new_child(env_key);
                    for (param_name, param_ty) in param_names.iter().zip(param_tys.iter()) {
                        //println!("Setting function env {param} = {arg}");
                        env.set(new_env_key, param_name.clone(), param_ty.clone(), true);
                    }

                    let body = list.next().unwrap();
                    let body_ty = typecheck(body, env, new_env_key)?;
                    if !ret_ty.compatible(&body_ty, &mut Default::default()) {
                        return Err(EvalError::TypeMismatch { expected: format!("{}", ret_ty), got: body_ty, span: body.tag.clone() });
                    }

                    let method_ty = Type::Method { params: param_tys, ret: Box::new(ret_ty) };

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

pub fn eval_static(
    node: SpanNode,
    env: &mut Environment,
    env_key: EnvironmentKey
) -> Result<SpanNode, EvalError> {
    match node.node {
        NodeValue::Bool(_)
            | NodeValue::Number(_)
            | NodeValue::String(_)
            | NodeValue::Keyword(_)
            | NodeValue::Symbol(_)
            | NodeValue::Type(_)
            | NodeValue::Typed(_, _) => Ok(node),
        NodeValue::List(ref list) => {
            if list.borrow().len() == 0 {
                Ok(node)
            } else {
                let mut list = list.borrow_mut();
                let func_symbol = list.first().cloned().unwrap();
                let mut list_iter = list.iter_mut();
                if let Some(func_symbol) = func_symbol.as_symbol() {
                    if func_symbol.as_str() == "static" {
                        let val = list_iter.nth(1).unwrap();
                        return eval(val.clone(), env, env_key);
                    } else if let Some(node) = env.get(env_key, func_symbol).cloned() {
                        if node.ty() == Type::Function {
                            let methods = node.as_typed().unwrap().1.as_list().unwrap().borrow();
                            for method in methods.iter().map(|m| m.as_method().unwrap().borrow()) {
                                match &*method {
                                    Method::Rust { ty: Type::Macro, callback } => {
                                        //let args = list_iter.skip(1).map(|n| eval_static(n.clone(), env)).collect::<Result<Vec<_>, _>>()?.into_iter();
                                        let args = list_iter.skip(1).map(|n| n.clone()).collect::<Vec<_>>().into_iter();
                                        return eval_static(callback(args, env, env_key)?, env, env_key);
                                    }
                                    _ => continue
                                }
                            }
                        }
                    }
                }
                for elem in list_iter {
                    let _ = mem::replace(elem, eval_static(elem.clone(), env, env_key)?);
                }
                drop(list);
                Ok(node)
            }
        },
        NodeValue::Table(ref table) => {
            {
                let mut t = mem::take(&mut *table.borrow_mut());
                t = t.into_iter().map(|(key, val)| {
                    Ok::<_, EvalError>((
                        eval_static(key, env, env_key)?,
                        eval_static(val, env, env_key)?
                    ))
                }).collect::<Result<IndexMap<_, _>, _>>()?;
                let _ = mem::replace(&mut *table.borrow_mut(), t);
            }
            Ok(node)
        },
        _ => todo!("{node}")
    }
}

fn main() {
    let filename = env::args().nth(1).expect("Expected file argument");
    let src = fs::read_to_string(&filename).expect("Failed to read file");

    let mut files = SimpleFiles::new();
    let file = files.add(filename, &src);
    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    // Tokenize and parse to node tree
    let mut lexer = Token::lexer(src.as_str());
    let tree = match parse_block(&mut lexer) {
        Ok(tree) => tree,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("parse: {e}"));

            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
            return;
        }
    };
    println!("Tree: {tree}");

    // Eval
    let mut runtime_env = Environment::new();
    let global_key = runtime_env.global;
    runtime_env.global_set("Unit".into(), Node::new_type(Default::default(), Type::Unit));
    runtime_env.global_set("Any".into(), Node::new_type(Default::default(), Type::Any));
    runtime_env.global_set("Type".into(), Node::new_type(Default::default(), Type::Type(None)));
    runtime_env.global_set("Unknown".into(), Node::new_type(Default::default(), Type::Unknown));
    runtime_env.global_set("Number".into(), Node::new_type(Default::default(), Type::Number));
    runtime_env.global_set("Bool".into(), Node::new_type(Default::default(), Type::Bool));
    runtime_env.global_set("String".into(), Node::new_type(Default::default(), Type::String));
    runtime_env.global_set("Function".into(), Node::new_type(Default::default(), Type::Number));

    // Special forms
    runtime_env.global_def_special_form("list".into(), Box::new(|args, env, env_key| {
        let span = args.clone().next().unwrap().tag.clone();
        Ok(Node::new_list(
            span,
            Reference::new(args.map(|arg| eval(arg, env, env_key)).collect::<Result<Vec<_>, _>>()?)
        ))
    }));
    runtime_env.global_def_special_form("loop".into(), Box::new(|mut args, env, env_key| {
        let body = args.next().unwrap();
        loop {
            if let NodeValue::Bool(b) = eval(body.clone(), env, env_key)?.node {
                if b { break; }
            }
        }
        Ok(Node::new_list(Default::default(), Reference::new(vec![])))
    }));
    runtime_env.global_def_special_form("do".into(), Box::new(|mut args, env, env_key| {
        // Create a new scope
        let new_env_key = env.new_child(env_key);
        let mut res = Node::new_list(Default::default(), Reference::new(Vec::new()));

        while let Some(arg) = args.next() {
            res = eval(arg, env, new_env_key)?;
        }
        Ok(res)
    }));
    runtime_env.global_def_special_form("quote".into(), Box::new(|mut args, env, env_key| {
        Ok(args.next().unwrap())
    }));
    runtime_env.global_def_special_form("static".into(), Box::new(|mut args, env, env_key| {
        let mut res = Node::new_list(Default::default(), Reference::new(Vec::new()));

        if let Some(arg) = args.next() {
            res = eval(arg, env, env_key)?;
        }
        Ok(res)
    }));
    runtime_env.global_def_special_form("get".into(), Box::new(|mut args, env, env_key| {
        let (ty, var) = eval(args.next().unwrap(), env, env_key)?.with_type();
        let key = args.next().unwrap();

        if let NodeValue::Table(map) = var.node {
            Ok(map.borrow().get(&key).unwrap().clone())
        } else if let NodeValue::List(list) = var.node {
            Ok(list.borrow().get(key.into_number().unwrap() as usize).unwrap().clone())
        } else {
            panic!("Can only get from table/list objects, got: {var}")
        }
    }));
    runtime_env.global_def_special_form("let".into(), Box::new(|mut args, env, env_key| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env, env_key)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.set(env_key, name.clone(), value, true);
        }
        Ok(name)
    }));
    runtime_env.global_def_special_form("set".into(), Box::new(|mut args, env, env_key| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env, env_key)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.set(env_key, name.clone(), value, false);
        }
        Ok(name)
    }));
    runtime_env.global_def_special_form("global-set".into(), Box::new(|mut args, env, env_key| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env, env_key)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.global_set(name.clone(), value);
        }
        Ok(name)
    }));
    runtime_env.global_def_special_form("def".into(), Box::new(|mut args, env, env_key| {
        let name_symbol = args.next().unwrap();
        let method = eval(args.next().unwrap(), env, env_key)?;
        assert!(method.is_method());

        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.global_def(name.clone(), method);
        }
        Ok(name_symbol)
    }));
    runtime_env.global_def_special_form("local-def".into(), Box::new(|mut args, env, env_key| {
        let name_symbol = args.next().unwrap();

        let mut list = vec![Node::new_symbol(Default::default(), "fn".into())];
        list.extend(args);

        let value = eval(Node::new_list(name_symbol.tag.clone(), Reference::new(list)), env, env_key)?;
        assert!(value.is_method());
        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.def(env_key, name.clone(), value);
        }
        Ok(name_symbol)
    }));
    runtime_env.global_def_special_form("call".into(), Box::new(|mut args, env, env_key| {
        let func_symbol = args.next().unwrap();
        Ok(eval_call(func_symbol.clone(), eval(func_symbol, env, env_key)?, args, env, env_key)?)
    }));
    runtime_env.global_def_special_form("fn".into(), Box::new(|mut args, env, env_key| {
        let params = args.next().unwrap(); // let params = eval(args.next().unwrap(), env)?;
        let arrow = args.next().unwrap();
        arrow.node.as_symbol().filter(|s| **s == "->").ok_or(EvalError::Generic(arrow.tag))?;
        let ret_ty = eval(args.next().unwrap(), env, env_key)?;
        let block = args.next().unwrap();

        if !params.is_table() {
            return Err(EvalError::TypeMismatch { expected: "Table".to_string(), got: params.ty(), span: params.tag });
        }

        let params = params.into_table()
            .map_err(|n| EvalError::TypeMismatch { expected: "Table".to_string(), got: n.ty(), span: n.tag })?;
        let params = params.borrow();

        let mut parse_param_type = |node: &SpanNode| -> Result<Type, EvalError> {
            Ok(eval(node.clone(), env, env_key)?.into_type().unwrap())
        };

        let func_ty = Type::Method {
            params: params.values().map(|v| parse_param_type(v)).collect::<Result<_, _>>()?,
            ret: Box::new(ret_ty.into_type().map_err(|n| {
                EvalError::TypeMismatch { expected: "Type".to_string(), got: n.ty(), span: n.tag }
            })?)
        };
        Ok(Node::new_method(block.tag.clone(), Reference::new(Method::Hop {
            param_names: params.keys().cloned().map(|n| n.into_keyword().unwrap()).collect(),
            env: env_key, body: Box::new(block), ty: func_ty
        })))
    }));
    runtime_env.global_def_special_form("if".into(), Box::new(|mut args, env, env_key| {
        let cond = eval(args.next().unwrap(), env, env_key)?;
        let yes = args.next().unwrap();
        let mut no = None;
        if let Some(else_symbol) = args.next() {
            no = Some(args.next().unwrap());
        }

        if cond.into_bool().unwrap() {
            Ok(eval(yes, env, env_key)?)
        } else if let Some(no) = no {
            Ok(eval(no, env, env_key)?)
        } else {
            Ok(Node::new_list(Default::default(), Reference::new(vec![])))
        }
    }));
    runtime_env.global_def_special_form("imp".into(), Box::new(|mut args, env, env_key| {
        let elem: Vec<SpanNode> = args.collect();

        let func_name = elem[0].node.as_symbol().unwrap().clone();
        let param_types: Vec<Type> = elem[1..elem.len()-2].iter().map(|e| {
            Ok::<_, EvalError>(eval(e.clone(), env, env_key)?.into_type().unwrap())
        }).collect::<Result<_, _>>()?;
        let ret_type = eval(elem.last().unwrap().clone(), env, env_key)?.into_type().unwrap();

        let imp = Implementation {
            func: func_name,
            params: param_types,
            ret: Box::new(ret_type)
        };

        //Ok(Node::new_type(Default::default(), Type::Implements(implementations)))
        Ok(Node::new_implementation(elem[0].tag.clone(), imp))
    }));

    // Methods
    runtime_env.global_def_rust_method("+".into(), Box::new(|mut args, env, env_key| {
        let a = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_string(Default::default(), (a.to_string() + b.as_str()).into()))
    }), Type::Method { params: vec![Type::String, Type::String], ret: Box::new(Type::String) });
    runtime_env.global_def_rust_method("+".into(), Box::new(|mut args, env, env_key| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a + b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    runtime_env.global_def_rust_method("-".into(), Box::new(|mut args, env, env_key| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a - b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    runtime_env.global_def_rust_method("lt".into(), Box::new(|mut args, env, env_key| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a < b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    runtime_env.global_def_rust_method("=".into(), Box::new(|mut args, env, env_key| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a == b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Bool) });
    runtime_env.global_def_rust_method("refeq".into(), Box::new(|mut args, env, env_key| {
        let a = eval(args.next().unwrap(), env, env_key)?;
        let b = eval(args.next().unwrap(), env, env_key)?;
        Ok(Node::new_bool(Default::default(), a == b))
    }), Type::Method { params: vec![Type::Any, Type::Any], ret: Box::new(Type::Bool) });
    let out = Rc::new(RefCell::new(BufWriter::new(std::io::stdout())));
    runtime_env.global_def_rust_method("print".into(), Box::new(move |mut args, env, env_key| {
        let value = args.next().unwrap();
        //writeln!(out.borrow_mut(), "{value}");
        println!("{value}");
        Ok(value)
    }), Type::Method { params: vec![Type::Any], ret: Box::new(Type::Any) });
    runtime_env.global_def_rust_method("struct".into(), Box::new(|mut args, env, env_key| {
        let structure = args.next().unwrap();
        assert!(structure.is_table());

        Ok(Node::new_type(Default::default(), Type::Struct(
            Box::new(structure)
        )))
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Type(None)) });
    runtime_env.global_def_rust_method("enum".into(), Box::new(|mut args, env, env_key| {
        let enumeration = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::Enum(
            Box::new(enumeration)
        )))
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Type(None)) });
    /*global_env.def_rust_method("List".into(), Box::new(|mut args, env| {
        let ty = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::List(
            Box::new(ty.into_type().unwrap())
        )))
    }), Type::Method { params: vec![Type::Type], ret: Box::new(Type::Type) });*/

    // Macros
    runtime_env.global_def_rust_macro("def!".into(), Box::new(|mut args, env, env_key| {
        let name_symbol = args.next().unwrap();
        let params = args.next().unwrap();
        let arrow = args.next().unwrap();
        let ret_ty = eval(args.next().unwrap(), env, env_key)?;
        let block = args.next().unwrap();

        if let NodeValue::Table(ref table) = params.node {
            table.borrow_mut().values_mut().for_each(|val| {
                let mut tmp = Node::new_bool(Default::default(), false);
                mem::swap(val, &mut tmp);
                let mut new_val = Node::new_list(Default::default(), Reference::new(vec![
                    Node::new_symbol(Default::default(), "static".into()),
                    tmp
                ]));
                mem::swap(val, &mut new_val);
            });
        }

        Ok(Node::new_list(Default::default(), Reference::new(vec![
            Node::new_symbol(Default::default(), "def".into()),
            name_symbol, Node::new_list(Default::default(), Reference::new(vec![
                Node::new_symbol(Default::default(), "fn".into()),
                params, arrow, ret_ty, block
            ]))
        ])))
    }));
    runtime_env.global_def_rust_macro("new!".into(), Box::new(|mut args, env, env_key| {
        let ty = args.next().unwrap();
        let val = args.next().unwrap();

        Ok(Node::new_list(Default::default(), Reference::new(vec![
            Node::new_list(Default::default(), Reference::new(vec![
                Node::new_symbol(Default::default(), "static".into()),
                ty
            ])),
            val
        ])))
    }));

    // Static pass
    println!("Running static pass...");
    let tree = match eval_static(tree, &mut runtime_env, global_key) {
        Ok(t) => t,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("static: {e}"));

            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
            return;
        }
    };
    println!("Tree: {tree}");

    // Typecheck pass
    let mut type_env = TypeEnvironment::new();
    let env_key = type_env.global;
    for (k, v) in runtime_env.get_scope(runtime_env.global).unwrap().bindings.iter() {
        //println!("SETTING TE {k} = {v} i.e. {}", v.ty());
        type_env.set(env_key, k.clone(), v.ty(), false);
        if v.ty().is_function() {
            for method in v.as_typed().unwrap().1.as_list().unwrap().borrow().iter() {
                //println!(" - {method}");
                type_env.def(env_key, k.clone(), method.ty());
            }
        }
    }
    if let Err(e) = typecheck(&tree, &mut type_env, env_key) {
        let diagnostic = Diagnostic::error()
            .with_labels(vec![
                Label::primary(file, e.span())
            ])
            .with_message(format!("typecheck: {e}"));

        let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        return;
    }

    // Main pass
    println!("Running main pass...");
    let result = eval(tree, &mut runtime_env, global_key);

    match result {
        Ok(r) => println!("Result: {r}"),
        Err(e) => {
            println!("{:?}", e);
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("runtime: {e}"));
        
            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();
        
            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        }
    }
}
