use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, fmt::{Debug, Display}, ops::Deref, rc::Rc};

use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use logos::Span;
use smol_str::SmolStr;

use crate::eval::{Environment, EvalError};

#[derive(Debug, PartialEq, Clone)]
pub struct Implementation {
    pub func: SmolStr,
    pub params: Vec<Type>,
    pub ret: Box<Type>
}
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
pub enum Type {
    Type(Box<Type>),
    Placeholder(Option<SmolStr>),
    Any,
    Unknown,
    Symbol,
    Bool,
    Number,
    String,

    UntypedList,
    UntypedTable,
    List(Box<Type>),
    Table(Box<Type>),
    Implements(Vec<Implementation>),

    Function, // List of methods
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
                        if func.ty().is_function() {
                            let list = func.with_type().1.into_list().unwrap();
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
pub struct Reference<T>(Rc<RefCell<T>>);
impl<T> Reference<T> {
    pub fn new(node: T) -> Self {
        Self(Rc::new(RefCell::new(node)))
    }
    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.borrow()
    }
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.borrow_mut()
    }
    pub fn cloned(&self) -> Self {
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
pub type Callback = dyn Fn(std::vec::IntoIter<SpanNode>, &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError>;
pub enum Method {
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
        match self {
            Self::Hop { ty, .. } | Self::Rust { ty, ..} => {
                let ty = ty.as_method().unwrap();
                write!(f, "method(")?;
                let mut it = ty.0.iter().peekable();
                while let Some(item) = it.next() {
                    if it.peek().is_none() {
                        write!(f, "{}", item)?;
                    } else {
                        write!(f, "{} ", item)?;
                    }
                }
                write!(f, ") -> {}", ty.1)
            }
        }
    }
}
impl Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Node<T: Clone> {
    pub tag: T,
    pub node: NodeValue<T>
}
impl<T: Clone> Deref for Node<T> {
    type Target = NodeValue<T>;
    fn deref(&self) -> &Self::Target {
        &self.node
    }
}
pub type SpanNode = Node<Span>;
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
pub enum NodeValue<T: Clone> {
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

            Self::Method(method) => write!(f, "{}", method.borrow()),
            Self::Type(ty) => write!(f, "<{ty}>"),
            Self::Typed(ty, node) => {
                write!(f, "<{ty}>/{node}")
            }
        }
    }
}
impl<T: Clone> Node<T> {
    pub fn new_symbol(tag: T, val: SmolStr) -> Self {
        Self { tag, node: NodeValue::Symbol(val) }
    }
    pub fn new_string(tag: T, val: SmolStr) -> Self {
        Self { tag, node: NodeValue::String(val) }
    }
    pub fn new_bool(tag: T, val: bool) -> Self {
        Self { tag, node: NodeValue::Bool(val) }
    }
    pub fn new_number(tag: T, val: f64) -> Self {
        Self { tag, node: NodeValue::Number(val) }
    }
    pub fn new_list(tag: T, val: Reference<Vec<Node<T>>>) -> Self {
        Self { tag, node: NodeValue::List(val) }
    }
    pub fn new_table(tag: T, val: Reference<IndexMap<SmolStr, Node<T>>>) -> Self {
        Self { tag, node: NodeValue::Table(val) }
    }
    pub fn new_method(tag: T, val: Reference<Method>) -> Self {
        Self { tag, node: NodeValue::Method(val) }
    }
    pub fn new_typed(tag: T, ty: Type, val: Node<T>) -> Self {
        Self { tag, node: NodeValue::Typed(ty, Box::new(val)) }
    }
    pub fn new_type(tag: T, ty: Type) -> Self {
        Self { tag, node: NodeValue::Type(ty) }
    }

    pub fn ty(&self) -> Type {
        match &self.node {
            NodeValue::Bool(_) => Type::Bool,
            NodeValue::Number(_) => Type::Number,
            NodeValue::String(_) => Type::String,
            NodeValue::Symbol(_) => Type::Symbol,
            NodeValue::List(_) => Type::UntypedList,
            NodeValue::Table(_) => Type::UntypedTable,

            NodeValue::Typed(ty, _) => ty.clone(),
            NodeValue::Type(ty) => Type::Type(Box::new(ty.clone())),
            _ => unimplemented!("ty {self}")
        }
    }
    pub fn with_type(self) -> (Type, Node<T>) {
        match self.node {
            NodeValue::Typed(ty, node) => (ty, *node),
            _ => (self.ty(), self)
        }
    }

    pub fn into_bool(self) -> Result<bool, Self> {
        self.node.into_bool().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_number(self) -> Result<f64, Self> {
        self.node.into_number().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_symbol(self) -> Result<SmolStr, Self> {
        self.node.into_symbol().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_string(self) -> Result<SmolStr, Self> {
        self.node.into_string().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_method(self) -> Result<Reference<Method>, Self> {
        self.node.into_method().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_type(self) -> Result<Type, Self> {
        self.node.into_type().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_list(self) -> Result<Reference<Vec<Self>>, Node<T>> {
        self.node.into_list().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_table(self) -> Result<Reference<IndexMap<SmolStr, Self>>, Node<T>> {
        self.node.into_table().map_err(|val| Self { tag: self.tag, node: val })
    }
    pub fn into_typed(self) -> Result<(Type, Box<Self>), Node<T>> {
        self.node.into_typed().map_err(|val| Self { tag: self.tag, node: val })
    }
}