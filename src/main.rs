use codespan_reporting::{diagnostic::{Diagnostic, Label}, files::SimpleFiles, term::termcolor::{ColorChoice, StandardStream}};
use eval::{Environment, EvalError};
use logos::{Logos, Span};
use smol_str::SmolStr;
use thiserror::Error;
use std::{cell::RefCell, collections::HashMap, env, fs, io::BufWriter, mem, rc::Rc};

mod tokenize;
use tokenize::{parse_block, Token};
mod ast;
use ast::{Implementation, Method, Node, NodeValue, Reference, SpanNode, Type};
mod eval;
use eval::{eval, eval_call};

#[derive(Error, Debug)]
pub enum TypeCheckError {
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
impl TypeCheckError {
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
pub struct TypeEnvironment {
    bindings: HashMap<SmolStr, Type>,
    functions: HashMap<SmolStr, Vec<Type>>,
    up: Option<Rc<RefCell<Self>>>,
    global: Option<Rc<RefCell<Self>>>
}
impl TypeEnvironment {
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

    pub fn get(&self, name: &SmolStr) -> Option<Type> {
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
    pub fn set(&mut self, name: SmolStr, value: Type, shadow: bool) {
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
    pub fn def(&mut self, name: SmolStr, value: Type) {
        if self.functions.contains_key(&name) {
            self.functions.get_mut(&name).unwrap().push(value);
        } else {
            self.functions.insert(name, vec![value]);
        }
    }

    pub fn global_get(&mut self, name: &SmolStr) -> Option<Type> {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().get(name)
        } else {
            self.get(name)
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
    }
}

fn typecheck(node: &SpanNode, env: &Rc<RefCell<TypeEnvironment>>) -> Result<Type, TypeCheckError> {
    match &node.node {
        NodeValue::Bool(_) => Ok(Type::Bool),
        NodeValue::Number(_) => Ok(Type::Number),
        NodeValue::String(_) => Ok(Type::String),
        NodeValue::Symbol(name) => {
            Ok(env.borrow_mut().get(&name).ok_or(TypeCheckError::UndefinedVar { span: node.tag.clone() })?.clone())
        },
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
                        last = typecheck(elem, env)?;
                    }
                    Ok(last)
                },
                Some("set") => {
                    let symbol = list.next().unwrap().node.as_symbol().unwrap();
                    let val = list.next().unwrap();
                    env.borrow_mut().set(symbol.clone(), typecheck(val, env)?, false);
                    Ok(Type::UntypedList)
                },
                Some("struct") => {
                    let table = list.next().unwrap();
                    Ok(Type::Type(Box::new(
                        Type::Struct(Box::new(table.clone()))
                    )))
                },
                Some("def") => {
                    let func = list.next().unwrap();
                    let params = list.next().unwrap();
                    let arrow = list.next().unwrap();
                    let ret_ty = list.next().unwrap();

                    env.borrow_mut().functions.insert(
                        func.as_symbol().unwrap().clone(),
                        vec![
                            Type::Method { params: vec![], ret: Box::new(Type::UntypedList) }
                        ]
                    );

                    Ok(Type::UntypedList)
                },
                Some(func) => {
                    if env.borrow().functions.contains_key(func) {
                        Ok(*env.borrow().functions[func][0].as_method().unwrap().1.clone())
                    } else {
                        todo!()
                    }
                },
                _ => {
                    //let first = typecheck(first, env)?;
                    Ok(Type::UntypedList)
                }
            }
        },
        _ => todo!()
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
    println!("Tree: {}", tree);

    /*let type_env = TypeEnvironment::default();
    let type_env_rc = Rc::new(RefCell::new(type_env));
    if let Err(e) = typecheck(&tree, &type_env_rc) {
        let diagnostic = Diagnostic::error()
            .with_labels(vec![
                Label::primary(file, e.span())
            ])
            .with_message(format!("typecheck: {e}"));

        let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        return;
    }*/

    // Eval
    let mut global_env = Environment::default();
    global_env.global_set("Any".into(), Node::new_type(Default::default(), Type::Any));
    global_env.global_set("Unknown".into(), Node::new_type(Default::default(), Type::Unknown));
    global_env.global_set("Number".into(), Node::new_type(Default::default(), Type::Number));
    global_env.global_set("Bool".into(), Node::new_type(Default::default(), Type::Bool));
    global_env.global_set("String".into(), Node::new_type(Default::default(), Type::String));
    global_env.global_set("Function".into(), Node::new_type(Default::default(), Type::Number));
    global_env.def_rust_macro("_".into(), Box::new(|args, env| {
        let span = args.clone().next().unwrap().tag.clone();
        Ok(Node::new_list(
            span,
            Reference::new(args.map(|arg| eval(arg, env)).collect::<Result<Vec<_>, _>>()?)
        ))
    }));
    global_env.def_rust_method("+".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_string(Default::default(), (a.to_string() + b.as_str()).into()))
    }), Type::Method { params: vec![Type::String, Type::String], ret: Box::new(Type::String) });
    global_env.def_rust_method("+".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a + b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("-".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a - b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("lt".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a < b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("=".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a == b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Bool) });
    global_env.def_rust_macro("loop".into(), Box::new(|mut args, env| {
        let body = args.next().unwrap();
        loop {
            if let NodeValue::Bool(b) = eval(body.clone(), env)?.node {
                if b { break; }
            }
        }
        Ok(Node::new_list(Default::default(), Reference::new(vec![])))
    }));
    global_env.def_rust_macro("do".into(), Box::new(|mut args, env| {
        // Create a new scope
        let new_env = Environment::new_child(Rc::clone(env));
        let new_env_rc = Rc::new(RefCell::new(new_env));
        let mut res = Node::new_list(Default::default(), Reference::new(Vec::new()));

        while let Some(arg) = args.next() {
            res = eval(arg, &new_env_rc)?;
        }
        Ok(res)
    }));
    global_env.def_rust_macro("get".into(), Box::new(|mut args, env| {
        let (ty, var) = eval(args.next().unwrap(), env)?.with_type();
        let key = args.next().unwrap();

        if let NodeValue::Table(map) = var.node {
            Ok(map.borrow().get(key.as_symbol().unwrap()).unwrap().clone())
        } else if let NodeValue::List(list) = var.node {
            Ok(list.borrow().get(*key.as_number().unwrap() as usize).unwrap().clone())
        } else {
            panic!("Can only get from table/list objects, got: {var}")
        }
    }));
    global_env.def_rust_macro("let".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().set(name.clone(), value, true);
        }
        Ok(name)
    }));
    global_env.def_rust_macro("set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().set(name.clone(), value, false);
        }
        Ok(name)
    }));
    global_env.def_rust_macro("global-set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().global_set(name.clone(), value);
        }
        Ok(name)
    }));
    global_env.def_rust_macro("def".into(), Box::new(|mut args, env| {
        let name_symbol = args.next().unwrap();

        let mut list = vec![Node::new_symbol(Default::default(), "fn".into())];
        list.extend(args);

        let value = eval(Node::new_list(name_symbol.tag.clone(), Reference::new(list)), env)?;
        assert!(value.is_method());
        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.borrow_mut().global_def(name.clone(), value);
        }
        Ok(name_symbol)
    }));
    global_env.def_rust_macro("local-def".into(), Box::new(|mut args, env| {
        let name_symbol = args.next().unwrap();

        let mut list = vec![Node::new_symbol(Default::default(), "fn".into())];
        list.extend(args);

        let value = eval(Node::new_list(name_symbol.tag.clone(), Reference::new(list)), env)?;
        assert!(value.is_method());
        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.borrow_mut().def(name.clone(), value);
        }
        Ok(name_symbol)
    }));
    global_env.def_rust_macro("call".into(), Box::new(|mut args, env| {
        let func_symbol = args.next().unwrap();
        Ok(eval_call(func_symbol.clone(), eval(func_symbol, env)?, args, env)?)
    }));
    global_env.def_rust_macro("fn".into(), Box::new(|mut args, env| {
        let params = args.next().unwrap(); // let params = eval(args.next().unwrap(), env)?;
        let arrow = args.next().unwrap();
        arrow.node.as_symbol().filter(|s| **s == "->").ok_or(EvalError::Generic(arrow.tag))?;
        let ret_ty = eval(args.next().unwrap(), env)?;
        let block = args.next().unwrap();

        if !params.is_table() {
            return Err(EvalError::TypeMismatch { expected: "Table".to_string(), got: params.ty(), span: params.tag });
        }

        let params = params.into_table()
            .map_err(|n| EvalError::TypeMismatch { expected: "Table".to_string(), got: n.ty(), span: n.tag })?;
        let params = params.borrow();

        let parse_param_type = |node: &SpanNode| -> Result<Type, EvalError> {
            Ok(eval(node.clone(), env)?.into_type().unwrap())
        };

        let func_ty = Type::Method {
            params: params.values().map(|v| parse_param_type(v)).collect::<Result<_, _>>()?,
            ret: Box::new(ret_ty.into_type().map_err(|n| {
                EvalError::TypeMismatch { expected: "Type".to_string(), got: n.ty(), span: n.tag }
            })?)
        };
        Ok(Node::new_method(block.tag.clone(), Reference::new(Method::Hop {
            param_names: params.keys().cloned().collect(),
            env: Rc::clone(env), body: Box::new(block), ty: func_ty
        })))
    }));
    global_env.def_rust_macro("if".into(), Box::new(|mut args, env| {
        let cond = eval(args.next().unwrap(), env)?;
        let yes = args.next().unwrap();
        let else_symbol = args.next().unwrap();
        let no = args.next().unwrap();

        if cond.into_bool().unwrap() {
            Ok(eval(yes, env)?)
        } else {
            Ok(eval(no, env)?)
        }
    }));
    let out = Rc::new(RefCell::new(BufWriter::new(std::io::stdout())));
    global_env.def_rust_method("print".into(), Box::new(move |mut args, env| {
        let value = args.next().unwrap();
        //writeln!(out.borrow_mut(), "{value}");
        println!("{value}");
        Ok(value)
    }), Type::Method { params: vec![Type::Any], ret: Box::new(Type::Any) });
    global_env.def_rust_method("struct".into(), Box::new(|mut args, env| {
        let structure = args.next().unwrap();
        assert!(structure.is_table());
        // let structure: Result<IndexMap<_, _>, Box<dyn Error>> =
        //     structure.borrow_mut().into_iter().map(|(k, v)| {
        //         Ok((k, eval(v, env)?.into_type().unwrap()))
        //     }).collect();

        Ok(Node::new_type(Default::default(), Type::Struct(
            Box::new(structure)
        )))
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Unknown) });
    /*global_env.def_rust_method("List".into(), Box::new(|mut args, env| {
        let ty = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::List(
            Box::new(ty.into_type().unwrap())
        )))
    }), Type::Method { params: vec![Type::Type], ret: Box::new(Type::Type) });*/
    global_env.def_rust_macro("imp".into(), Box::new(|mut args, env| {
        let mut implementations = Vec::new();
        for elem in args {
            let elem = elem.node.as_list().unwrap();
            let elem = elem.borrow();

            let func_name = elem[0].node.as_symbol().unwrap().clone();
            let param_types: Vec<Type> = elem[1..elem.len()-2].iter().map(|e| {
                if e.is_symbol() && e.node.as_symbol().unwrap().starts_with("_") {
                    let placeholder_name = e.node.as_symbol().unwrap().split_at(1).1;
                    Ok(Type::Placeholder(if placeholder_name.len() == 0 { None } else { Some(placeholder_name.into()) }))
                } else {
                    Ok::<_, EvalError>(eval(e.clone(), env)?.into_type().unwrap())
                }
            }).collect::<Result<_, _>>()?;
            let ret_type = eval(elem.last().unwrap().clone(), env)?.into_type().unwrap();

            let imp = Implementation {
                func: func_name,
                params: param_types,
                ret: Box::new(ret_type)
            };
            implementations.push(imp);
        }
        println!("Implements {:?}", implementations);
        Ok(Node::new_type(Default::default(), Type::Implements(implementations)))
    }));

    let global_env_rc = Rc::new(RefCell::new(global_env));
    let result = eval(tree, &global_env_rc);

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
