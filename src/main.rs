use codespan_reporting::{diagnostic::{Diagnostic, Label}, files::{SimpleFile, SimpleFiles}, term::termcolor::{ColorChoice, StandardStream}};
use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use logos::{Lexer, Logos, Span};
use thiserror::Error;
use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, default, env, error::Error, fmt::{Debug, Display}, fs, io::{BufWriter, Write}, mem, ops::Index, rc::Rc};
use smol_str::SmolStr;

#[derive(Error, Debug)]
enum ParseError {
    #[error("unexpected token, got {got:?}")]
    UnexpectedToken {
        got: Token,
        span: Span
    },
    #[error("expected symbol, got {got:?}")]
    ExpectedSymbol {
        got: Token,
        span: Span
    },
    #[error("expected list, got {got:?}")]
    ExpectedList {
        got: Node,
        span: Span
    },
    #[error("TODO: custom error message")]
    Generic(Span)
}
impl ParseError {
    fn span(&self) -> Span {
        match self {
            Self::ExpectedList { span, .. } |
            Self::UnexpectedToken { span, .. } |
            Self::ExpectedSymbol { span, .. } |
            Self::Generic(span) => span.clone(),
        }
    }
}
#[derive(Error, Debug)]
enum EvalError {
    #[error("error in rust callback, {error}")]
    RustCallback { error: Box<dyn Error>, span: Span },
    #[error("type mismatch: expected type {expected} got {got}")]
    TypeMismatch { expected: Type, got: Type, span: Span },
    #[error("TODO: custom error message")]
    Generic(Span)
}
impl EvalError {
    fn span(&self) -> Span {
        match self {
            Self::RustCallback { span, .. } |
            Self::TypeMismatch { span, .. } |
            Self::Generic(span) => span.clone()
        }
    }
}

#[derive(Debug, Logos)]
#[logos(skip r"[ \t\r\n\f]+")] // Ignore whitespace
#[logos(skip r"//[^\r\n]*(\r\n|\n)?")] // Ignore comments
enum Token {
    #[token("{")]
    BlockOpen,
    #[token("}")]
    BlockClose,

    #[token("(")]
    ListOpen,
    #[token(")")]
    ListClose,

    #[token("[")]
    TableOpen,
    #[token("]")]
    TableClose,

    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,

    #[token("false", |_| false)]
    #[token("true", |_| true)]
    Bool(bool),

    #[regex(r"-?(\d+(\.\d*)?|\.\d+)", |lex| lex.slice().parse::<f64>().unwrap(), priority = 2)]
    Number(f64),

    #[regex(r#""([^"\\]|\\["\\bnfrt]|u[a-fA-F0-9]{4})*""#, |lex| {
        let m = lex.slice();
        SmolStr::from(&m[1..(m.len() - 1)])
    })]
    String(SmolStr),

    #[regex(r#"[a-zA-Z\-\/+_]+"#, |lex| SmolStr::from(lex.slice()))]
    Symbol(SmolStr),

    // Sugar
    #[regex(r#"\.\("#)]
    Call,

    #[token(".")]
    Deref,
}

#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Type {
    Type,
    Symbol,
    Bool,
    Number,
    String,

    Untyped,
    UntypedList,
    UntypedTable,
    List(Box<Type>),
    Table(Box<Type>),
    Implements(Vec<SmolStr>),

    Method {
        params: Box<Node>,
        ret: Box<Type>
    },
    Struct(Box<Node>)
}
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
        // match self {
        //     Self::Primitive => write!(f, "PRIMITIVE"),
        //     Self::Struct(structure) => {
        //         write!(f, "STRUCT[ ")?;
        //         for (key, value) in structure.iter() {
        //             key.fmt(f)?;
        //             write!(f, ": ")?;
        //             value.fmt(f)?;
        //             write!(f, " ")?;
        //         }
        //         write!(f, "]")
        //     }
        // }
    }
}
#[derive(Debug)]
struct Reference<T>(Rc<RefCell<T>>);
impl<T> Reference<T> {
    fn new(node: T) -> Self {
        Self(Rc::new(RefCell::new(node)))
    }
    fn borrow(&self) -> Ref<'_, T> {
        self.0.borrow()
    }
    fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.borrow_mut()
    }
    fn cloned(&self) -> Self {
        Reference(Rc::clone(&self.0))
    }
}
impl<T> Clone for Reference<T> {
    fn clone(&self) -> Self {
        self.cloned()
    }
}
impl<T> PartialEq for Reference<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl<T: Display> Display for Reference<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.borrow().fmt(f)
    }
}
type Callback = dyn Fn(std::vec::IntoIter<Node>, &Rc<RefCell<Environment>>) -> Result<Node, Box<dyn Error>>;
enum Method {
    Hop {
        env: Rc<RefCell<Environment>>,
        tree: Box<Node>,
        ty: Type
    },
    Rust(Box<Callback>)
}
impl Debug for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn()")
    }
}
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Node {
    Symbol(SmolStr),
    Bool(bool),
    Number(f64),
    String(SmolStr),
    List(Reference<Vec<Node>>),
    Table(Reference<IndexMap<SmolStr, Node>>),

    Method(Reference<Method>), // Each function is a list of methods (for multiple dispatch)
    Type(Type/*, Vec<Node>*/),
    Typed(Type, Box<Node>), // (Type, Node)
}
impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(val) => write!(f, "{val}"),
            Self::Number(val) => write!(f, "{val}"),
            Self::String(val) => write!(f, r#""{val}""#),
            Self::Symbol(val) => write!(f, "'{val}"),
            Self::List(list) => {
                write!(f, "( ")?;
                for item in list.borrow().iter() {
                    write!(f, "{item} ")?;
                }
                write!(f, ")")
            },
            Self::Table(list) => {
                write!(f, "[ ")?;
                for (key, value) in list.borrow().iter() {
                    write!(f, "{key}: {value} ")?;
                }
                write!(f, "]")
            },

            Self::Method {..} => write!(f, "fn()"),
            Self::Type(ty) => write!(f, "<{ty}>"),
            Self::Typed(ty, node) => {
                write!(f, "<{ty}>/{node}")
            }
        }
    }
}
impl Node {
    fn new_list(val: Vec<Node>) -> Self {
        Self::List(Reference::new(val))
    }
    fn new_table(val: IndexMap<SmolStr, Node>) -> Self {
        Self::Table(Reference::new(val))
    }
    fn with_type(self) -> (Type, Node) {
        match self {
            Self::Bool(val) => (Type::Bool, Node::Bool(val)),
            Self::Number(val) => (Type::Number, Node::Number(val)),
            Self::String(val) => (Type::String, Node::String(val)),
            Self::Symbol(val) => (Type::Symbol, Node::Symbol(val)),
            Self::List(val) => (Type::UntypedList, Node::List(val)),
            Self::Table(val) => (Type::UntypedTable, Node::Table(val)),

            Self::Type(ty) => (Type::Type, Node::Type(ty)),
            Self::Typed(ty, node) => (ty, *node),
            _ => unimplemented!("with_type {self}")
        }
    }
}

// foo(1 2 3) -> (call foo (1 2 3))
fn parse_call(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, ParseError> {
    let l = parse_list(lexer)?;
    let l = l.into_list().map_err(|_| ParseError::Generic(lexer.span()))?;
    let mut res = vec![Node::Symbol("call".into()), lhs];
    res.append(&mut l.borrow_mut());
    Ok(Node::new_list(res))
}
// foo.bar.baz -> (get (get foo bar) baz)
fn parse_deref(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, ParseError> {
    let token = lexer.next().ok_or(ParseError::Generic(lexer.span()))?.unwrap();
    match token {
        Token::Symbol(rhs) => {
            Ok(Node::new_list(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        _ => Err(ParseError::ExpectedSymbol { got: token, span: lexer.span() })
    }
}
// [a: "hi", b: 2]
fn parse_table(lexer: &mut Lexer<'_, Token>) -> Result<Node, ParseError> {
    let mut res: IndexMap<SmolStr, Node> = IndexMap::new();
    let mut want_key = true;
    let mut key: SmolStr = SmolStr::default();

    while let Some(Ok(token)) = lexer.next() {
        if want_key {
            want_key = false;
            match token {
                Token::TableClose => return Ok(Node::Table(Reference::new(res))),
                Token::Symbol(str) => key = str.into(),
                Token::Colon | Token::Comma => want_key = true,
                token => return Err(ParseError::ExpectedSymbol { got: token, span: lexer.span() })
            };
        } else {
            want_key = true;
            match token {
                Token::ListOpen => {res.insert(mem::take(&mut key), parse_list(lexer)?);},
                Token::BlockOpen => {res.insert(mem::take(&mut key), parse_block(lexer)?);},
                Token::TableOpen => {res.insert(mem::take(&mut key), parse_table(lexer)?);},
    
                Token::Bool(bool) => {res.insert(mem::take(&mut key), Node::Bool(bool));},
                Token::Number(num) => {res.insert(mem::take(&mut key), Node::Number(num));},
                Token::String(str) => {res.insert(mem::take(&mut key), Node::String(str));},
                Token::Symbol(str) => {res.insert(mem::take(&mut key), Node::Symbol(str));},

                // Token::Deref => {
                //     assert!(res.len() > 1);
                //     let lhs = res.remove(res.len() - 1);
                //     res.insert(mem::take(&mut key), parse_deref(lexer, Node::Symbol(str))?);
                // },

                Token::Colon | Token::Comma => want_key = false,
                token => return Err(ParseError::UnexpectedToken { got: token, span: lexer.span() })
            };
        }
    }
    Ok(Node::Table(Reference::new(res)))
}
// (a 123 false)
fn parse_list(lexer: &mut Lexer<'_, Token>) -> Result<Node, ParseError> {
    let mut res: Vec<Node> = Vec::new();

    while let Some(token) = lexer.next() {
        match token.map_err(|_| ParseError::Generic(lexer.span()))? {
            Token::ListClose => return Ok(Node::List(Reference::new(res))),

            Token::ListOpen => res.push(parse_list(lexer)?),
            Token::BlockOpen => res.push(parse_block(lexer)?),
            Token::TableOpen => res.push(parse_table(lexer)?),

            Token::Bool(bool) => res.push(Node::Bool(bool)),
            Token::Number(num) => res.push(Node::Number(num)),
            Token::String(str) => res.push(Node::String(str)),
            Token::Symbol(str) => res.push(Node::Symbol(str)),

            Token::Call => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = res.remove(res.len() - 1);
                res.push(parse_call(lexer, lhs)?)
            },
            Token::Deref => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = res.remove(res.len() - 1);
                res.push(parse_deref(lexer, lhs)?)
            },
            token => return Err(ParseError::UnexpectedToken { got: token, span: lexer.span() })
        }
    }
    Ok(Node::List(Reference::new(res)))
}
// A block is like a list but each semicolon-separated line gets it's own list
// {
//    print "hi";
//    + 1 2
//      3 4;
//    42
// }
// becomes
// [ do [print "hi"] [+ 1 2 3 4] [42] ]
fn parse_block(lexer: &mut Lexer<'_, Token>) -> Result<Node, ParseError> {
    let mut res: Vec<Node> = Vec::new();
    res.push(Node::Symbol("do".into()));
    let mut list: Vec<Node> = Vec::new();

    while let Some(token) = lexer.next() {
        match token.map_err(|_| ParseError::Generic(lexer.span()))? {
            Token::BlockClose => {
                if list.len() == 1 {
                    res.push(list.into_iter().next().unwrap());
                } else {
                    res.push(Node::new_list(list));
                }
                return Ok(Node::new_list(res))
            },
            Token::Semicolon => {
                let list = mem::take(&mut list);
                if list.len() == 1 {
                    res.push(list.into_iter().next().unwrap());
                } else {
                    res.push(Node::new_list(list));
                }
            },

            Token::ListOpen => list.push(parse_list(lexer)?),
            Token::TableOpen => list.push(parse_table(lexer)?),
            Token::BlockOpen => list.push(parse_block(lexer)?),

            Token::Bool(bool) => list.push(Node::Bool(bool)),
            Token::Number(num) => list.push(Node::Number(num)),
            Token::String(str) => list.push(Node::String(str)),
            Token::Symbol(str) => list.push(Node::Symbol(str)),

            Token::Call => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = list.remove(list.len() - 1);
                list.push(parse_call(lexer, lhs)?)
            },
            Token::Deref => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = list.remove(list.len() - 1);
                list.push(parse_deref(lexer, lhs)?)
            },
            token => return Err(ParseError::UnexpectedToken { got: token, span: lexer.span() })
        }
    }
    if list.len() == 1 {
        res.push(list.into_iter().next().unwrap());
    } else {
        res.push(Node::new_list(list));
    }
    Ok(Node::new_list(res))
}

#[derive(Default, Debug, PartialEq)]
struct Environment {
    bindings: HashMap<SmolStr, Node>,
    up: Option<Rc<RefCell<Environment>>>
}
impl Environment {
    fn get(&self, name: &SmolStr) -> Option<Node> {
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
    fn has(&self, name: &SmolStr) -> bool {
        self.get(name).is_some()
    }
    fn set(&mut self, name: SmolStr, value: Node) {
        if self.has(&name) {
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
    fn def(&mut self, name: SmolStr, func: Box<Callback>) {
        let func = Node::Method(Reference::new(Method::Rust(func)));
        if self.has(&name) {
            self.get(&name).unwrap().into_list().unwrap().borrow_mut().push(func);
        } else {
            self.set(name.clone(), Node::List(Reference::new(vec![func])));
        }
    }
}

fn eval_call(func: Node, mut args: impl Iterator<Item = Node>, env: &Rc<RefCell<Environment>>) -> Result<Node, EvalError> {
    if let Node::List(methods) = func {
        let methods: Vec<Reference<Method>> = methods.borrow().iter().cloned().map(|m| m.into_method().unwrap()).collect();
        
        let rust_func = methods.first().map(|m| matches!(*m.borrow(), Method::Rust(_))).unwrap_or_default();
        let (call_tys, call_args): (Vec<_>, Vec<_>) =
            args.map(|arg| {
                if rust_func {
                    Ok(arg.with_type())
                } else {
                    Ok::<_, EvalError>(eval(arg, env)?.with_type())
                }
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter().unzip();

        for method in methods {
            let borrowed = method.borrow();
            match &*borrowed {
                Method::Hop { env, tree, ty } => {
                    let method_ty = ty.clone().into_method().unwrap();
                    let method_param_table = method_ty.0.into_table().unwrap();
                    let method_param_table_rc = method_param_table.borrow();
                    let method_param_names = method_param_table_rc.keys().collect::<Vec<_>>();
                    let method_param_tys = method_param_table_rc.values().map(|v| v.clone().into_type().unwrap()).collect::<Vec<_>>();
                    let param_count = method_param_tys.len();

                    // Method match
                    if call_tys.iter().zip(&method_param_tys).filter(|&(a, b)| a == b).count() == param_count {
                        // Call method
                        // Create a new scope
                        let mut new_env = Environment {
                            up: Some(Rc::clone(&env)),
                            ..Default::default()
                        };

                        for (param, arg) in method_param_names.into_iter().zip(call_args.into_iter()) {
                            // println!("Setting function env {param} = {arg}");
                            new_env.set(param.clone(), arg);
                        }

                        let new_env_rc = Rc::new(RefCell::new(new_env));
                        let (res_ty, res) = eval(*tree.clone(), &new_env_rc)?.with_type();
                        return if res_ty == *method_ty.1 {
                            Ok(res)
                        } else {
                            Err(EvalError::TypeMismatch { expected: res_ty, got: *method_ty.1, span: 0..1 })
                        };
                    }
                },
                Method::Rust(f) => return f(call_args.into_iter(), env).map_err(|e| EvalError::RustCallback { error: e, span: 0..1 })
            }
        }
        panic!("No method matches found when calling func!")
    } else if let Node::Type(ty) = func {
        // Create type instance
        let val = eval(args.next().unwrap(), env)?;
        Ok(Node::Typed(ty, Box::new(val)))
    } else {
        panic!("Attempted to call non-function variable <{func}> as function")
    }
}
fn eval(node: Node, env: &Rc<RefCell<Environment>>) -> Result<Node, EvalError> {
    match node {
        Node::Bool(_) | Node::Number(_) | Node::String(_) | Node::Type(_) => Ok(node),
        Node::Symbol(name) => {
            Ok(env.borrow_mut().get(&name).expect(
                 &format!("Attempted to dereference invalid variable {name}")
            ).clone())
        },
        Node::List(list) if list.borrow().len() == 0 => Ok(Node::List(list)),
        Node::List(list) => {
            if list.borrow().len() == 0 {
                Ok(Node::List(list))
            } else {
                let list = list.borrow();
                let func = eval(list.first().cloned().unwrap(), env)?;
                let args = list.iter().cloned().skip(1);
                eval_call(func, args, env)
            }
        },
        Node::Table(table) => {
            {
                let mut table = table.borrow_mut();
                table.values_mut().map(|val| {
                    let _ = mem::replace(val, eval(val.clone(), env)?);
                    Ok::<_, EvalError>(())
                }).collect::<Result<(), _>>()?;
            }
            Ok(Node::Table(table))
        },
        _ => todo!("{node}")
    }
}

fn main() {
    let filename = env::args().nth(1).expect("Expected file argument");
    let src = fs::read_to_string(&filename).expect("Failed to read file");

    let mut files = SimpleFiles::new();
    let file = files.add(filename, &src);

    // Tokenize and parse to node tree
    let mut lexer = Token::lexer(src.as_str());
    let tree = match parse_block(&mut lexer) {
        Ok(tree) => tree,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("{e}"));

            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();

            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
            return;
        }
    };
    println!("Tree: {}", tree);

    // Eval
    let mut global_env = Environment::default();
    global_env.bindings.insert("Number".into(), Node::Type(Type::Number));
    global_env.bindings.insert("Bool".into(), Node::Type(Type::Bool));
    global_env.bindings.insert("String".into(), Node::Type(Type::String));
    global_env.bindings.insert("Type".into(), Node::Type(Type::Type));
    global_env.bindings.insert("Function".into(), Node::Type(Type::Number));
    global_env.def("_".into(), Box::new(|args, env| {
        Ok(Node::new_list(args.map(|arg| eval(arg, env)).collect::<Result<Vec<_>, _>>()?))
    }));
    global_env.def("+".into(), Box::new(|mut args, env| {
        let a = eval(args.next().unwrap(), env)?.into_number().unwrap();
        let b = eval(args.next().unwrap(), env)?.into_number().unwrap();
        Ok(Node::Number(a + b))
    }));
    global_env.def("-".into(), Box::new(|mut args, env| {
        let a = eval(args.next().unwrap(), env)?.into_number().unwrap();
        let b = eval(args.next().unwrap(), env)?.into_number().unwrap();
        Ok(Node::Number(a - b))
    }));
    global_env.def("lt".into(), Box::new(|mut args, env| {
        let a = eval(args.next().unwrap(), env)?.into_number().unwrap();
        let b = eval(args.next().unwrap(), env)?.into_number().unwrap();
        Ok(Node::Bool(a < b))
    }));
    global_env.def("loop".into(), Box::new(|mut args, env| {
        let body = args.next().unwrap();
        loop {
            if let Node::Bool(b) = eval(body.clone(), env)? {
                if b { break; }
            }
        }
        Ok(Node::new_list(vec![]))
    }));
    global_env.def("do".into(), Box::new(|mut args, env| {
        // Create a new scope
        let new_env = Environment {
            up: Some(Rc::clone(env)),
            ..Default::default()
        };
        let new_env_rc = Rc::new(RefCell::new(new_env));
        let mut res = Node::new_list(Vec::new());

        while let Some(arg) = args.next() {
            res = eval(arg, &new_env_rc)?;
        }
        Ok(res)
    }));
    global_env.def("set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let Node::Symbol(ref name) = name {
            env.borrow_mut().set(name.clone(), value);
        }
        Ok(name)
    }));
    global_env.def("get".into(), Box::new(|mut args, env| {
        let (ty, var) = eval(args.next().unwrap(), env)?.with_type();
        let key = args.next().unwrap();

        if let Node::Table(map) = var {
            Ok(map.borrow().get(key.as_symbol().unwrap()).unwrap().clone())
        } else if let Node::List(list) = var {
            Ok(list.borrow().get(*key.as_number().unwrap() as usize).unwrap().clone())
        } else {
            panic!("Can only get from table/list objects, got: {var}")
        }
    }));
    global_env.def("def".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        assert!(value.is_method());
        if let Node::Symbol(ref name) = name {
            if env.borrow().has(name) {
                env.borrow_mut().get(name).unwrap().into_list().unwrap().borrow_mut().push(value);
            } else {
                env.borrow_mut().set(name.clone(), Node::List(Reference::new(vec![value])));
            }
        }
        Ok(name)
    }));
    global_env.def("call".into(), Box::new(|mut args, env| {
        Ok(eval_call(eval(args.next().unwrap(), env)?, args, env)?)
    }));
    global_env.def("fn".into(), Box::new(|mut args, env| {
        let params = eval(args.next().unwrap(), env)?;
        let ret_ty = eval(args.next().unwrap(), env)?;
        let block = args.next().unwrap();

        assert!(params.is_table());
        let func_ty = Type::Method { params: Box::new(params), ret: Box::new(ret_ty.into_type().unwrap()) };
        Ok(Node::Method(Reference::new(Method::Hop { env: Rc::clone(env), tree: Box::new(block), ty: func_ty })))
    }));
    global_env.def("if".into(), Box::new(|mut args, env| {
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
    global_env.def("print".into(), Box::new(move |mut args, env| {
        let value = eval(args.next().unwrap(), env)?;
        //writeln!(out.borrow_mut(), "{value}");
        println!("{value}");
        Ok(value)
    }));
    global_env.def("struct".into(), Box::new(|mut args, env| {
        let structure = eval(args.next().unwrap(), env)?;
        assert!(structure.is_table());
        // let structure: Result<IndexMap<_, _>, Box<dyn Error>> =
        //     structure.borrow_mut().into_iter().map(|(k, v)| {
        //         Ok((k, eval(v, env)?.into_type().unwrap()))
        //     }).collect();

        Ok(Node::Type(Type::Struct(
            Box::new(structure)
        )))
    }));
    global_env.def("List".into(), Box::new(|mut args, env| {
        let ty = eval(args.next().unwrap(), env)?;

        Ok(Node::Type(Type::List(
            Box::new(ty.into_type().unwrap())
        )))
    }));
    global_env.def("imp".into(), Box::new(|mut args, env| {
        //let funcs: Vec<_> = args.map(|a| eval(a, env)).collect::<Result<_, _>>()?;
        let funcs: Vec<_> = args.map(|a| a.into_symbol()).collect::<Result<_, _>>().unwrap();

        Ok(Node::Type(Type::Implements(
            funcs
        )))
    }));

    let global_env_rc = Rc::new(RefCell::new(global_env));
    println!("Result: {}", eval(tree, &global_env_rc).unwrap());
}
