use codespan_reporting::{diagnostic::{Diagnostic, Label}, files::{SimpleFile, SimpleFiles}, term::termcolor::{ColorChoice, StandardStream}};
use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use logos::{Lexer, Logos, Span};
use thiserror::Error;
use std::{borrow::Cow, cell::{Ref, RefCell, RefMut}, collections::HashMap, default, env, error::Error, fmt::{Debug, Display}, fs, io::{BufWriter, Write}, mem, ops::{Deref, Index}, rc::Rc};
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
        got: SpanNode,
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
    fn span(&self) -> Span {
        match self {
            Self::TypeMismatch { span, .. } |
            Self::NoMethodMatches { span, .. } |
            Self::CalledNonFunc { span, .. } |
            Self::UndefinedVar { span, .. } |
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

    #[token("<")]
    InfixOpen,
    #[token(">")]
    InfixClose,

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

    #[regex(r#"[a-zA-Z\-\/+_=]+[a-zA-Z\-\/+_=><]*"#, |lex| SmolStr::from(lex.slice()))]
    Symbol(SmolStr),

    // Sugar
    #[regex(r#"\.\("#)]
    Call,

    #[token(".")]
    Deref,
}

#[derive(Debug, PartialEq, Clone)]
struct Implementation {
    func: SmolStr,
    params: Vec<Type>,
    ret: Box<Type>
}
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Type {
    Placeholder(Option<SmolStr>),
    Any,
    Unknown,
    Type,
    Symbol,
    Bool,
    Number,
    String,

    UntypedList,
    UntypedTable,
    List(Box<Type>),
    Table(Box<Type>),
    Implements(Vec<Implementation>),

    Method {
        params: Vec<Type>,
        ret: Box<Type>
    },
    Struct(Box<SpanNode>)
}
impl Type {
    pub fn compatible(self: &Type, rhs: &Type, env: &Environment, placeholder_matches: &mut HashMap<SmolStr, Type>) -> bool {
        if self == rhs { return true; }
        match rhs {
            Self::Any | Self::Unknown => return true,
            _ => ()
        };
        match self {
            Self::Any | Self::Unknown => true,
            Self::Implements(implementations) => {
                for imp in implementations {
                    if let Some(func) = env.get(&imp.func) {
                        if let Ok(list) = func.into_list() {
                            let list = list.borrow();
                            let list = list.iter().map(|l| l.node.as_method().unwrap());

                            let mut found_match = false;
                            'outer: for method in list {
                                let method = method.borrow();
                                match &*method {
                                    Method::Rust { ty, .. } | Method::Hop { ty, .. } => {
                                        let method_ty = ty.as_method().unwrap();
                                        //println!("CHECKING METHOD {method_ty:?}");
                                        // First check arity and return type to quickly eliminate invalid matches
                                        if imp.params.len() != method_ty.0.len() { continue; }
                                        if !imp.ret.compatible(method_ty.1, env, placeholder_matches) { continue; }
                                        // Then check all parameters in order
                                        for (a, b) in imp.params.iter().zip(method_ty.0.iter()) {
                                            // If we have a placeholder, fill it
                                            let a = match *a {
                                                // Empty placeholders automatically get filled with the matched type
                                                Type::Placeholder(None) => rhs,
                                                // Named placeholders get filled the first time they match
                                                Type::Placeholder(Some(ref placeholder_name)) => {
                                                    // If it's already filled, use that type
                                                    if let Some(pt) = placeholder_matches.get(placeholder_name) {
                                                        if pt != rhs {
                                                            continue 'outer;
                                                        } else {
                                                            rhs
                                                        }
                                                    } else {
                                                        placeholder_matches.insert(placeholder_name.clone(), rhs.clone());
                                                        rhs
                                                    }
                                                },
                                                _ => a
                                            };
                                            // println!("{a} vs. {b} ULTIMATE SHOWDOWN");
                                            // println!("RESULT!!!! {}", a.compatible(b, env, placeholder_matches));
                                            if !a.compatible(b, env, placeholder_matches) { continue 'outer; }
                                        }
                                        // println!("FOUND MATCH!!!!");
                                        found_match = true;
                                        break 'outer;
                                    }
                                }
                            }
                            if !found_match { return false; }
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            },
            Self::UntypedList => match rhs {
                Self::UntypedList | Self::List(_) => true,
                _ => false
            },
            _ => false
        }
    }
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
type Callback = dyn Fn(std::vec::IntoIter<SpanNode>, &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError>;
enum Method {
    Hop {
        param_names: Vec<SmolStr>,
        env: Rc<RefCell<Environment>>,
        body: Box<SpanNode>,
        ty: Type
    },
    Rust {
        callback: Box<Callback>,
        ty: Type
    }
}
impl Debug for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn()")
    }
}

#[derive(Debug, PartialEq, Clone)]
struct Node<T: Clone> {
    tag: T,
    node: NodeValue<T>
}
impl<T: Clone> Deref for Node<T> {
    type Target = NodeValue<T>;
    fn deref(&self) -> &Self::Target {
        &self.node
    }
}
type SpanNode = Node<Span>;
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum NodeValue<T: Clone> {
    Symbol(SmolStr),
    Bool(bool),
    Number(f64),
    String(SmolStr),
    List(Reference<Vec<Node<T>>>),
    Table(Reference<IndexMap<SmolStr, Node<T>>>),

    Method(Reference<Method>), // Each function is a list of methods (for multiple dispatch)
    Type(Type),
    Typed(Type, Box<Node<T>>), // (Type, Node)
}
impl<T: Clone> Display for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}
impl<T: Clone> Display for NodeValue<T> {
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
impl<T: Clone> Node<T> {
    fn new_symbol(tag: T, val: SmolStr) -> Self {
        Self { tag, node: NodeValue::Symbol(val) }
    }
    fn new_string(tag: T, val: SmolStr) -> Self {
        Self { tag, node: NodeValue::String(val) }
    }
    fn new_bool(tag: T, val: bool) -> Self {
        Self { tag, node: NodeValue::Bool(val) }
    }
    fn new_number(tag: T, val: f64) -> Self {
        Self { tag, node: NodeValue::Number(val) }
    }
    fn new_list(tag: T, val: Reference<Vec<Node<T>>>) -> Self {
        Self { tag, node: NodeValue::List(val) }
    }
    fn new_table(tag: T, val: Reference<IndexMap<SmolStr, Node<T>>>) -> Self {
        Self { tag, node: NodeValue::Table(val) }
    }
    fn new_method(tag: T, val: Reference<Method>) -> Self {
        Self { tag, node: NodeValue::Method(val) }
    }
    fn new_typed(tag: T, ty: Type, val: Node<T>) -> Self {
        Self { tag, node: NodeValue::Typed(ty, Box::new(val)) }
    }
    fn new_type(tag: T, ty: Type) -> Self {
        Self { tag, node: NodeValue::Type(ty) }
    }

    fn ty(&self) -> Type {
        match &self.node {
            NodeValue::Bool(_) => Type::Bool,
            NodeValue::Number(_) => Type::Number,
            NodeValue::String(_) => Type::String,
            NodeValue::Symbol(_) => Type::Symbol,
            NodeValue::List(_) => Type::UntypedList,
            NodeValue::Table(_) => Type::UntypedTable,

            NodeValue::Type(_) => Type::Type,
            NodeValue::Typed(ty, _) => ty.clone(),
            _ => unimplemented!("ty {self}")
        }
    }
    fn with_type(self) -> (Type, Node<T>) {
        match self.node {
            NodeValue::Typed(ty, node) => (ty, *node),
            _ => (self.ty(), self)
        }
    }

    fn into_bool(self) -> Result<bool, Self> {
        self.node.into_bool().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_number(self) -> Result<f64, Self> {
        self.node.into_number().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_symbol(self) -> Result<SmolStr, Self> {
        self.node.into_symbol().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_string(self) -> Result<SmolStr, Self> {
        self.node.into_string().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_method(self) -> Result<Reference<Method>, Self> {
        self.node.into_method().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_type(self) -> Result<Type, Self> {
        self.node.into_type().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_list(self) -> Result<Reference<Vec<Self>>, Node<T>> {
        self.node.into_list().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_table(self) -> Result<Reference<IndexMap<SmolStr, Self>>, Node<T>> {
        self.node.into_table().map_err(|val| Self { tag: self.tag, node: val })
    }
    fn into_typed(self) -> Result<(Type, Box<Self>), Node<T>> {
        self.node.into_typed().map_err(|val| Self { tag: self.tag, node: val })
    }
}

// foo(1 2 3) -> (call foo (1 2 3))
fn parse_call(lexer: &mut Lexer<'_, Token>, lhs: SpanNode) -> Result<SpanNode, ParseError> {
    let l = parse_list(lexer)?;
    let l = l.node.into_list().map_err(|_| ParseError::Generic(lexer.span()))?;
    let mut res = vec![Node::new_symbol(lexer.span(), "call".into()), lhs];
    res.append(&mut l.borrow_mut());
    Ok(Node::new_list(lexer.span(), Reference::new(res)))
}
// foo.bar.baz -> (get (get foo bar) baz)
fn parse_deref(lexer: &mut Lexer<'_, Token>, lhs: SpanNode) -> Result<SpanNode, ParseError> {
    let token = lexer.next().ok_or(ParseError::Generic(lexer.span()))?.unwrap();
    match token {
        Token::Symbol(rhs) => {
            Ok(Node::new_list(
                lexer.span(), Reference::new(vec![Node::new_symbol(lexer.span(), "get".into()), lhs, Node::new_symbol(lexer.span(), rhs)])
            ))
        },
        _ => Err(ParseError::ExpectedSymbol { got: token, span: lexer.span() })
    }
}
// [a: "hi", b: 2]
fn parse_table(lexer: &mut Lexer<'_, Token>) -> Result<SpanNode, ParseError> {
    let mut table: IndexMap<SmolStr, SpanNode> = IndexMap::new();
    let mut want_key = true;
    let mut key: SmolStr = SmolStr::default();
    let start = lexer.span().start;

    let mut res: Vec<SpanNode> = Vec::new();
    while let Some(Ok(token)) = lexer.next() {
        if want_key {
            match token {
                Token::Symbol(str) => key = str.into(),
                Token::Colon | Token::Comma => {
                    want_key = false;
                },
                Token::TableClose => {
                    return Ok(Node::new_table(start..lexer.span().end, Reference::new(table)))
                },
                token => return Err(ParseError::ExpectedSymbol { got: token, span: lexer.span() })
            };
        } else {
            match token {
                Token::ListOpen => res.push(parse_list(lexer)?),
                Token::BlockOpen => res.push(parse_block(lexer)?),
                Token::TableOpen => res.push(parse_table(lexer)?),
    
                Token::Bool(bool) => res.push(Node::new_bool(lexer.span(), bool)),
                Token::Number(num) => res.push(Node::new_number(lexer.span(), num)),
                Token::String(str) => res.push(Node::new_string(lexer.span(), str)),
                Token::Symbol(str) => res.push(Node::new_symbol(lexer.span(), str)),

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

                Token::Colon | Token::Comma => {
                    if res.len() == 1 {
                        table.insert(mem::take(&mut key), mem::take(&mut res).into_iter().next().unwrap());
                    } else {
                        table.insert(mem::take(&mut key), Node::new_list(
                            lexer.span(), Reference::new(mem::take(&mut res))
                        ));
                    }
                    want_key = true;
                },
                Token::TableClose => {
                    if res.len() == 1 {
                        table.insert(mem::take(&mut key), mem::take(&mut res).into_iter().next().unwrap());
                    } else {
                        table.insert(mem::take(&mut key), Node::new_list(
                            lexer.span(), Reference::new(mem::take(&mut res))
                        ));
                    }
                    return Ok(Node::new_table(start..lexer.span().end, Reference::new(table)))
                },
                token => return Err(ParseError::UnexpectedToken { got: token, span: lexer.span() })
            };
        }
    }
    Ok(Node::new_table(start..lexer.span().end, Reference::new(table)))
}
// (a 123 false)
fn parse_list(lexer: &mut Lexer<'_, Token>) -> Result<SpanNode, ParseError> {
    let mut res: Vec<SpanNode> = Vec::new();
    let start = lexer.span().start;

    while let Some(token) = lexer.next() {
        match token.map_err(|_| ParseError::Generic(lexer.span()))? {
            Token::ListClose => return Ok(Node::new_list(start..lexer.span().end, Reference::new(res))),

            Token::ListOpen => res.push(parse_list(lexer)?),
            Token::BlockOpen => res.push(parse_block(lexer)?),
            Token::TableOpen => res.push(parse_table(lexer)?),

            Token::Bool(bool) => res.push(Node::new_bool(lexer.span(), bool)),
            Token::Number(num) => res.push(Node::new_number(lexer.span(), num)),
            Token::String(str) => res.push(Node::new_string(lexer.span(), str)),
            Token::Symbol(str) => res.push(Node::new_symbol(lexer.span(), str)),

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
    Ok(Node::new_list(start..lexer.span().end, Reference::new(res)))
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
fn parse_block(lexer: &mut Lexer<'_, Token>) -> Result<SpanNode, ParseError> {
    let mut res: Vec<SpanNode> = Vec::new();
    res.push(Node::new_symbol(lexer.span(), "do".into()));
    let mut list: Vec<SpanNode> = Vec::new();
    let start = lexer.span().start;

    while let Some(token) = lexer.next() {
        match token.map_err(|_| ParseError::Generic(lexer.span()))? {
            Token::BlockClose => {
                if list.len() == 1 {
                    res.push(list.into_iter().next().unwrap());
                } else {
                    res.push(Node::new_list(lexer.span(), Reference::new(list)));
                }
                return Ok(Node::new_list(start..lexer.span().end, Reference::new(res)))
            },
            Token::Semicolon => {
                let list = mem::take(&mut list);
                res.push(Node::new_list(lexer.span(), Reference::new(list)));
            },

            Token::ListOpen => list.push(parse_list(lexer)?),
            Token::TableOpen => list.push(parse_table(lexer)?),
            Token::BlockOpen => list.push(parse_block(lexer)?),

            Token::Bool(bool) => list.push(Node::new_bool(lexer.span(), bool)),
            Token::Number(num) => list.push(Node::new_number(lexer.span(), num)),
            Token::String(str) => list.push(Node::new_string(lexer.span(), str)),
            Token::Symbol(str) => list.push(Node::new_symbol(lexer.span(), str)),

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
        res.push(Node::new_list(lexer.span(), Reference::new(list)));
    }
    Ok(Node::new_list(start..lexer.span().end, Reference::new(res)))
}

#[derive(Default, Debug, PartialEq)]
struct Environment {
    bindings: HashMap<SmolStr, SpanNode>,
    up: Option<Rc<RefCell<Environment>>>,
    global: Option<Rc<RefCell<Environment>>>
}
impl Environment {
    fn new_child(this: Rc<RefCell<Self>>) -> Self {
        Environment {
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

    fn get(&self, name: &SmolStr) -> Option<SpanNode> {
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
    fn set(&mut self, name: SmolStr, value: SpanNode) {
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
    fn def(&mut self, name: SmolStr, value: SpanNode) {
        if self.has(&name) {
            self.get(&name).unwrap().into_list().unwrap().borrow_mut().push(value);
        } else {
            self.set(name.clone(), Node::new_list(Default::default(), Reference::new(vec![value])));
        }
    }

    fn global_get(&mut self, name: &SmolStr) -> Option<SpanNode> {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().get(name)
        } else {
            self.get(name)
        }
    }
    fn global_set(&mut self, name: SmolStr, value: SpanNode) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().set(name, value);
        } else {
            self.set(name, value);
        }
    }
    fn global_def(&mut self, name: SmolStr, value: SpanNode) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().def(name, value);
        } else {
            self.def(name, value);
        }
    }

    fn def_rust_method(&mut self, name: SmolStr, value: Box<Callback>, ty: Type) {
        self.def(name, Node::new_method(Default::default(), Reference::new(
            Method::Rust { callback: value, ty }
        )))
    }
    fn def_rust_macro(&mut self, name: SmolStr, value: Box<Callback>) {
        self.def_rust_method(name, value, Type::Unknown);
    }
}

fn eval_call(func_symbol: SpanNode, func: SpanNode, mut args: impl Iterator<Item = SpanNode>, env: &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError> {
    if let NodeValue::List(methods) = func.node {
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
                            new_env.set(param.clone(), arg);
                        }

                        let new_env_rc = Rc::new(RefCell::new(new_env));
                        let res = eval(*body.clone(), &new_env_rc)?;
                        let res_ty = res.ty();
                        return if method_ret_ty.compatible(&res_ty, &*env.borrow(), &mut placeholder_matches) {
                            Ok(res)
                        } else {
                            Err(EvalError::TypeMismatch { expected: format!("{}", res_ty), got: *method_ret_ty, span: body_tag })
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
fn eval(node: SpanNode, env: &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError> {
    match node.node {
        NodeValue::Bool(_) | NodeValue::Number(_) | NodeValue::String(_) | NodeValue::Type(_) => Ok(node),
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

fn typecheck(node: &SpanNode) -> Result<Type, ()> {
    match &node.node {
        NodeValue::Bool(_) => Ok(Type::Bool),
        NodeValue::Number(_) => Ok(Type::Number),
        NodeValue::String(_) => Ok(Type::String),
        NodeValue::Symbol(_) => todo!("typecheck symbol"),
        NodeValue::List(list) => {
            let list = list.borrow();
            if list.len() == 0 { return Ok(Type::UntypedList); }
            let mut list = list.iter();
            let first = list.next().unwrap();
            let first = first.node.as_symbol().unwrap();

            match first.as_str() {
                "do" => {
                    let mut last = Type::UntypedList;
                    while let Some(elem) = list.next() {
                        last = typecheck(elem)?;
                    }
                    Ok(last)
                },
                "set" => {
                    let symbol = list.next().unwrap();
                    let val = list.next().unwrap();
                    todo!("set")
                },
                _ => unimplemented!("{}", node)
            }
        },
        _ => Err(())
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

    //typecheck(&tree).unwrap();

    // Eval
    let mut global_env = Environment::default();
    global_env.bindings.insert("Any".into(), Node::new_type(Default::default(), Type::Any));
    global_env.bindings.insert("Unknown".into(), Node::new_type(Default::default(), Type::Unknown));
    global_env.bindings.insert("Number".into(), Node::new_type(Default::default(), Type::Number));
    global_env.bindings.insert("Bool".into(), Node::new_type(Default::default(), Type::Bool));
    global_env.bindings.insert("String".into(), Node::new_type(Default::default(), Type::String));
    global_env.bindings.insert("Type".into(), Node::new_type(Default::default(), Type::Type));
    global_env.bindings.insert("Function".into(), Node::new_type(Default::default(), Type::Number));
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
    global_env.def_rust_macro("set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().set(name.clone(), value);
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
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Type) });
    global_env.def_rust_method("List".into(), Box::new(|mut args, env| {
        let ty = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::List(
            Box::new(ty.into_type().unwrap())
        )))
    }), Type::Method { params: vec![Type::Type], ret: Box::new(Type::Type) });
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
                .with_message(format!("{e}"));
        
            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();
        
            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        }
    }
}
