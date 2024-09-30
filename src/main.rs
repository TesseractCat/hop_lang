use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use logos::{Lexer, Logos};
use slotmap::{new_key_type, SlotMap};
use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, default, env, error::Error, fmt::Display, fs, mem, ops::Index, rc::Rc};
use smol_str::SmolStr;

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

    #[regex(r"-?(\d|\.)+", |lex| lex.slice().parse::<f64>().unwrap())]
    Number(f64),

    #[regex(r#""([^"\\]|\\["\\bnfrt]|u[a-fA-F0-9]{4})*""#, |lex| {
        let m = lex.slice();
        SmolStr::from(&m[1..(m.len() - 1)])
    })]
    String(SmolStr),

    #[regex(r#"[a-zA-Z\-\/+_]+"#, |lex| SmolStr::from(lex.slice()))]
    Symbol(SmolStr),

    // Sugar
    #[regex(r#"[a-zA-Z\-\/+_]+\("#, |lex| {
        let m = lex.slice();
        SmolStr::from(&m[0..(m.len() - 1)])
    }, priority = 2)]
    Call(SmolStr),

    #[regex(r#"[a-zA-Z\-\/+_]+\."#, |lex| {
        let m = lex.slice();
        SmolStr::from(&m[0..(m.len() - 1)])
    }, priority = 3)]
    Deref(SmolStr)
}

#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Type {
    Type,
    Symbol,
    Bool,
    Number,
    String,
    List,
    Table,

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
#[derive(Debug, PartialEq, Clone)]
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
impl<T: Display> Display for Reference<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.borrow().fmt(f)
    }
}
#[derive(Debug, PartialEq, Clone)]
struct Function {
    env: Rc<RefCell<Environment>>,
    tree: Box<Node>,
    ty: Type
}
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Node {
    Symbol(SmolStr),
    Bool(bool),
    Number(f64),
    String(SmolStr),
    List(Reference<Vec<Node>>),
    Table(Reference<IndexMap<SmolStr, Node>>),

    Function(Reference<Vec<Function>>), // Each function is a vec of methods (for multiple dispatch)
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

            Self::Function {..} => write!(f, "fn()"),
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
            Self::List(val) => (Type::List, Node::List(val)),
            Self::Table(val) => (Type::Table, Node::Table(val)),

            Self::Type(ty) => (Type::Type, Node::Type(ty)),
            Self::Typed(ty, node) => (ty, *node),
            _ => unimplemented!("with_type {self}")
        }
    }
}

// foo(1 2 3) -> (call foo (1 2 3))
fn parse_call(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, Box<dyn Error>> {
    let l = parse_list(lexer)?.into_list().expect("Function calls must be followed by list");
    let mut res = vec![Node::Symbol("call".into()), lhs];
    res.append(&mut l.borrow_mut());
    Ok(Node::new_list(res))
}
// foo.bar.baz -> (get (get foo bar) baz)
fn parse_deref(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, Box<dyn Error>> {
    match lexer.next().unwrap().unwrap() {
        Token::Symbol(rhs) => {
            Ok(Node::new_list(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        Token::Deref(rhs) => {
            parse_deref(lexer, Node::new_list(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        Token::Call(rhs) => {
            parse_call(lexer, Node::new_list(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        _ => panic!("Deref rhs must be symbol")
    }
}
// [a: "hi", b: 2]
fn parse_table(lexer: &mut Lexer<'_, Token>) -> Result<Node, Box<dyn Error>> {
    let mut res: IndexMap<SmolStr, Node> = IndexMap::new();
    let mut want_key = true;
    let mut key: SmolStr = SmolStr::default();

    while let Some(token) = lexer.next() {
        if want_key {
            want_key = false;
            match token.unwrap() {
                Token::TableClose => return Ok(Node::Table(Reference::new(res))),
                Token::Symbol(str) => key = str.into(),
                Token::Colon | Token::Comma => want_key = true,
                x => panic!("Expected symbol while parsing table, got {x:?} at {:?}", lexer.span())
            };
        } else {
            want_key = true;
            match token.unwrap() {
                Token::ListOpen => {res.insert(mem::take(&mut key), parse_list(lexer)?);},
                Token::BlockOpen => {res.insert(mem::take(&mut key), parse_block(lexer)?);},
                Token::TableOpen => {res.insert(mem::take(&mut key), parse_table(lexer)?);},
    
                Token::Bool(bool) => {res.insert(mem::take(&mut key), Node::Bool(bool));},
                Token::Number(num) => {res.insert(mem::take(&mut key), Node::Number(num));},
                Token::String(str) => {res.insert(mem::take(&mut key), Node::String(str));},
                Token::Symbol(str) => {res.insert(mem::take(&mut key), Node::Symbol(str));},

                Token::Call(str) => {res.insert(mem::take(&mut key), parse_call(lexer, Node::Symbol(str))?);},
                Token::Deref(str) => {res.insert(mem::take(&mut key), parse_deref(lexer, Node::Symbol(str))?);},

                Token::Colon | Token::Comma => want_key = false,
                x => panic!("Unexpected token: {:?}", x)
            };
        }
    }
    Ok(Node::Table(Reference::new(res)))
}
// (a 123 false)
fn parse_list(lexer: &mut Lexer<'_, Token>) -> Result<Node, Box<dyn Error>> {
    let mut res: Vec<Node> = Vec::new();

    while let Some(token) = lexer.next() {
        match token.unwrap() {
            Token::ListClose => return Ok(Node::List(Reference::new(res))),

            Token::ListOpen => res.push(parse_list(lexer)?),
            Token::BlockOpen => res.push(parse_block(lexer)?),
            Token::TableOpen => res.push(parse_table(lexer)?),

            Token::Bool(bool) => res.push(Node::Bool(bool)),
            Token::Number(num) => res.push(Node::Number(num)),
            Token::String(str) => res.push(Node::String(str)),
            Token::Symbol(str) => res.push(Node::Symbol(str)),

            Token::Call(str) => res.push(parse_call(lexer, Node::Symbol(str))?),
            Token::Deref(str) => res.push(parse_deref(lexer, Node::Symbol(str))?),
            _ => panic!()
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
fn parse_block(lexer: &mut Lexer<'_, Token>) -> Result<Node, Box<dyn Error>> {
    let mut res: Vec<Node> = Vec::new();
    res.push(Node::Symbol("do".into()));
    let mut list: Vec<Node> = Vec::new();

    while let Some(token) = lexer.next() {
        match token.unwrap() {
            Token::BlockClose => {
                res.push(Node::new_list(list));
                return Ok(Node::new_list(res))
            },
            Token::Semicolon => res.push(Node::new_list(mem::take(&mut list))),

            Token::ListOpen => list.push(parse_list(lexer)?),
            Token::TableOpen => list.push(parse_table(lexer)?),
            Token::BlockOpen => list.push(parse_block(lexer)?),

            Token::Bool(bool) => list.push(Node::Bool(bool)),
            Token::Number(num) => list.push(Node::Number(num)),
            Token::String(str) => list.push(Node::String(str)),
            Token::Symbol(str) => list.push(Node::Symbol(str)),

            Token::Call(str) => list.push(parse_call(lexer, Node::Symbol(str))?),
            Token::Deref(str) => list.push(parse_deref(lexer, Node::Symbol(str))?),
            _ => panic!()
        }
    }
    res.push(Node::new_list(list));
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
        match value {
            value => self.bindings.insert(name, value.clone())
        };
    }
}

fn eval(node: Node, env: &Rc<RefCell<Environment>>) -> Result<Node, Box<dyn Error>> {
    match node {
        Node::Bool(_) | Node::Number(_) | Node::String(_) | Node::Type(_) => Ok(node),
        Node::Symbol(name) => {
            Ok(env.borrow_mut().get(&name).expect(
                 &format!("Attempted to dereference invalid variable {name}")
            ).clone())
        },
        Node::List(list) if list.borrow().len() == 0 => Ok(Node::List(list)),
        Node::List(list) => {
            let list = list.borrow_mut();
            if let Some(Node::Symbol(op)) = list.first().cloned() {
                let mut args = list.iter().cloned().skip(1);
                if op == "do" {
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
                } else if op == "set" {
                    let name = args.next().unwrap();
                    let value = eval(args.next().unwrap(), env)?;
                    if let Node::Symbol(ref name) = name {
                        env.borrow_mut().set(name.clone(), value);
                    }
                    Ok(name)
                } else if op == "get" {
                    let (ty, var) = eval(args.next().unwrap(), env)?.with_type();
                    let key = args.next().unwrap();

                    if let Node::Table(map) = var {
                        Ok(map.borrow().get(key.as_symbol().unwrap()).unwrap().clone())
                    } else if let Node::List(list) = var {
                        Ok(list.borrow().get(*key.as_number().unwrap() as usize).unwrap().clone())
                    } else {
                        panic!("Can only get from table/list objects, got: {var}")
                    }
                } else if op == "def" {
                    let name = args.next().unwrap();
                    let value = eval(args.next().unwrap(), env)?.into_function().unwrap().borrow_mut().iter().next().unwrap().clone();
                    if let Node::Symbol(ref name) = name {
                        if env.borrow().has(name) {
                            env.borrow_mut().get(name).unwrap().into_function().unwrap().borrow_mut().push(value);
                        } else {
                            env.borrow_mut().set(name.clone(), Node::Function(Reference::new(vec![value])));
                        }
                    }
                    Ok(name)
                } else if op == "call" {
                    let func = eval(args.next().unwrap(), env)?;
                    let (call_tys, call_args): (Vec<_>, Vec<_>) =
                        args.map(|arg| Ok::<_, Box<dyn Error>>(eval(arg, env)?.with_type()))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter().unzip();

                    if let Node::Function(methods) = func {
                        for method in methods.borrow().iter() {
                            assert!(method.ty.is_method());

                            let method_ty = method.ty.clone().into_method().unwrap();
                            let method_param_table = method_ty.0.into_table().unwrap();
                            let method_param_table_rc = method_param_table.borrow();
                            let method_param_names = method_param_table_rc.keys().collect::<Vec<_>>();
                            let method_param_tys = method_param_table_rc.values().map(|v| v.clone().into_type().unwrap()).collect::<Vec<_>>();
                            let param_count = method_param_tys.len();

                            // Method match
                            if call_tys.iter().zip(&method_param_tys).filter(|&(a, b)| a == b).count() == param_count {
                                // Call method
                                println!("Calling function {op}");
                                // Create a new scope
                                let mut new_env = Environment {
                                    up: Some(Rc::clone(&method.env)),
                                    ..Default::default()
                                };

                                for (param, arg) in method_param_names.into_iter().zip(call_args.into_iter()) {
                                    println!("Setting function env {param} = {arg}");
                                    new_env.set(param.clone(), arg);
                                }

                                let new_env_rc = Rc::new(RefCell::new(new_env));
                                return eval(*method.tree.clone(), &new_env_rc);
                            }
                        }
                        panic!("No method matches found when calling func!")
                    } else if let Node::Type(ty) = func {
                        // Create type instance
                        let val = call_args.into_iter().next().unwrap();
                        Ok(Node::Typed(ty, Box::new(val)))
                    } else {
                        panic!("Attempted to call non-function variable as function")
                    }
                } else if op == "fn" {
                    let params = eval(args.next().unwrap(), env)?;
                    let ret_ty = eval(args.next().unwrap(), env)?;
                    let block = args.next().unwrap();

                    assert!(params.is_table());
                    let func_ty = Type::Method { params: Box::new(params), ret: Box::new(ret_ty.into_type().unwrap()) };
                    Ok(Node::Function(Reference::new(vec![Function { env: Rc::clone(env), tree: Box::new(block), ty: func_ty }])))
                } else if op == "print" {
                    let value = eval(args.next().unwrap(), env)?;
                    println!("Print: {}", value);
                    Ok(value)
                } else if op == "struct" {
                    let structure = eval(args.next().unwrap(), env)?;
                    assert!(structure.is_table());
                    // let structure: Result<IndexMap<_, _>, Box<dyn Error>> =
                    //     structure.borrow_mut().into_iter().map(|(k, v)| {
                    //         Ok((k, eval(v, env)?.into_type().unwrap()))
                    //     }).collect();

                    Ok(Node::Type(Type::Struct(
                        Box::new(structure)
                    )))
                } else if op == "+" {
                    let a = eval(args.next().unwrap(), env)?;
                    let b = eval(args.next().unwrap(), env)?;
                    if let Node::Number(a) = a  {
                        if let Node::Number(b) = b {
                            return Ok(Node::Number(a + b));
                        }
                    }
                    todo!()
                } else {
                    unimplemented!()
                }
            } else {
                let mut res = Vec::with_capacity(list.len());
                for elem in list.iter() {
                    res.push(eval(elem.clone(), env)?);
                }
                Ok(Node::new_list(res))
            }
        },
        Node::Table(table) => {
            {
                let mut table = table.borrow_mut();
                table.values_mut().map(|val| {
                    let _ = mem::replace(val, eval(val.clone(), env)?);
                    Ok::<_, Box<dyn Error>>(())
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

    // Tokenize and parse to node tree
    let mut lexer = Token::lexer(src.as_str());
    let tree = parse_block(&mut lexer).unwrap();
    println!("Tree: {}", tree);

    // Eval
    let mut global_env = Environment::default();
    global_env.bindings.insert("Number".into(), Node::Type(Type::Number));
    global_env.bindings.insert("String".into(), Node::Type(Type::String));
    global_env.bindings.insert("Type".into(), Node::Type(Type::Type));
    global_env.bindings.insert("Function".into(), Node::Type(Type::Number));
    let global_env_rc = Rc::new(RefCell::new(global_env));
    println!("Result: {}", eval(tree, &global_env_rc).unwrap());
}
