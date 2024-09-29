use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use logos::{Lexer, Logos};
use slotmap::{new_key_type, SlotMap};
use std::{cell::{Ref, RefCell}, collections::HashMap, default, env, error::Error, fmt::Display, fs, mem, ops::Index, rc::Rc};
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

    #[regex(r#""([^"\\]|\\["\\bnfrt]|u[a-fA-F0-9]{4})*""#, |lex| SmolStr::from(lex.slice()))]
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

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Primitive,
    Struct(IndexMap<SmolStr, Node>)
}
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive => write!(f, "PRIMITIVE"),
            Self::Struct(structure) => {
                write!(f, "STRUCT[ ")?;
                for (key, value) in structure.iter() {
                    key.fmt(f)?;
                    write!(f, ": ")?;
                    value.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, "]")
            }
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
struct Reference(Rc<RefCell<Node>>);
impl Reference {
    fn new(node: Node) -> Self {
        Self(Rc::new(RefCell::new(node)))
    }
    fn borrow(&self) -> Ref<'_, Node> {
        self.0.borrow()
    }
    fn cloned(&self) -> Self {
        Reference(Rc::clone(&self.0))
    }
}
#[derive(Debug, PartialEq, Clone, EnumAsInner)]
enum Node {
    Symbol(SmolStr),
    Bool(bool),
    Number(f64),
    String(SmolStr),
    List(Vec<Node>),
    Table(IndexMap<SmolStr, Node>),

    Function {
        env: EnvironmentKey,
        tree: Box<Node>,
        params: Vec<SmolStr>,
    },
    Reference(Reference),
    Type(Type/*, Vec<Node>*/),
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
                for item in list.iter() {
                    item.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, ")")
            },
            Self::Table(list) => {
                write!(f, "[ ")?;
                for (key, value) in list.iter() {
                    key.fmt(f)?;
                    write!(f, ": ")?;
                    value.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, "]")
            },

            Self::Function {..} => write!(f, "FUNCTION"),
            Self::Reference(val) => {
                write!(f, "&")?;
                val.borrow().fmt(f)
            },
            Self::Type(ty) => ty.fmt(f),
        }
    }
}
impl Node {
    fn new_exp(func: &str, mut args: Vec<Node>) -> Self {
        args.insert(0, Node::Symbol(func.into()));
        Node::List(args)
    }
}

// foo(1 2 3) -> (call foo (1 2 3))
fn parse_call(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, Box<dyn Error>> {
    let l = parse_list(lexer)?.into_list().expect("Function calls must be followed by list");
    Ok(Node::List(vec![
        Node::Symbol("call".into()), lhs, Node::List(l)
    ]))
}
// foo.bar.baz -> (get (get foo bar) baz)
fn parse_deref(lexer: &mut Lexer<'_, Token>, lhs: Node) -> Result<Node, Box<dyn Error>> {
    match lexer.next().unwrap().unwrap() {
        Token::Symbol(rhs) => {
            Ok(Node::List(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        Token::Deref(rhs) => {
            parse_deref(lexer, Node::List(
                vec![Node::Symbol("get".into()), lhs, Node::Symbol(rhs)]
            ))
        },
        Token::Call(rhs) => {
            parse_call(lexer, Node::List(
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
                Token::TableClose => return Ok(Node::Table(res)),
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
    Ok(Node::Table(res))
}
// (a 123 false)
fn parse_list(lexer: &mut Lexer<'_, Token>) -> Result<Node, Box<dyn Error>> {
    let mut res: Vec<Node> = Vec::new();

    while let Some(token) = lexer.next() {
        match token.unwrap() {
            Token::ListClose => return Ok(Node::List(res)),

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
    Ok(Node::List(res))
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
                res.push(Node::List(list));
                return Ok(Node::List(res))
            },
            Token::Semicolon => res.push(Node::List(mem::take(&mut list))),

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
    res.push(Node::List(list));
    Ok(Node::List(res))
}

#[derive(Default)]
struct Environment {
    bindings: HashMap<SmolStr, Reference>,
    up: Option<Rc<RefCell<Environment>>>
}
impl Environment {
    fn get(&mut self, name: &SmolStr) -> Option<Node> {
        if let Some(binding) = self.bindings.get(name) {
            Some(Node::Reference(binding.cloned()))
        } else if let Some(up) = self.up.map(|r| Rc::clone(&r)) {
            let mut env = up;
            while env.borrow().bindings.get(name).is_none() {
                if let Some(up) = env.borrow().up {
                    env = up;
                } else {
                    break;
                }
            }
            env.borrow().bindings.get(name).map(|x| Node::Reference(x.cloned()))
        } else {
            None
        }
    }
}
fn env_get<'a>(env: EnvironmentKey, name: &SmolStr) -> Option<Node> {
    let mut env = key;
    while envs.get_mut(env).unwrap().bindings.get(name).is_none() {
        if let Some(up) = envs.get_mut(env).unwrap().up {
            env = up;
        } else {
            break;
        }
    }
    envs.get_mut(env).unwrap().bindings.get(name).map(|x| Node::Reference(x.cloned()))
}
fn env_set<'a>(envs: &'a mut SlotMap<EnvironmentKey, Environment>, key: EnvironmentKey, name: SmolStr, value: Node) {
    match value {
        Node::Reference(value) => envs.get_mut(key).unwrap().bindings.insert(name, value),
        value => envs.get_mut(key).unwrap().bindings.insert(name, Reference::new(value))
    };
}
fn eval(node: Node, envs: &mut SlotMap<EnvironmentKey, Environment>, key: EnvironmentKey) -> Result<Node, Box<dyn Error>> {
    match node {
        Node::Bool(_) | Node::Number(_) | Node::String(_) | Node::Table(_) => Ok(node),
        Node::Symbol(name) => {
            Ok(env_get(envs, key, &name).expect(
                 &format!("Attempted to dereference invalid variable {name}")
            ).clone())
        },
        Node::List(list) if list.len() == 0 => Ok(Node::List(list)),
        Node::List(mut list) => {
            if let Some(Node::Symbol(op)) = list.first().cloned() {
                let mut args = list.into_iter().skip(1);
                if op == "do" {
                    // Create a new scope
                    let env = Environment {
                        up: Some(key),
                        ..Default::default()
                    };
                    let new_key = envs.insert(env);
                    let mut res = Node::List(Vec::new());
                    while let Some(arg) = args.next() {
                        res = eval(arg, envs, new_key)?;
                    }
                    Ok(res)
                } else if op == "set" {
                    let name = args.next().unwrap();
                    let value = eval(args.next().unwrap(), envs, key)?;
                    let env = envs.get_mut(key).expect("Environment key invalid");
                    if let Node::Symbol(ref name) = name {
                        env_set(envs, key, name.clone(), value);
                    }
                    Ok(name)
                } else if op == "get" {
                    todo!()
                } else if op == "call" {
                    let func = eval(args.next().unwrap(), envs, key)?;
                    if let Node::Reference(func) = func {
                        if let Node::Function { env: func_env, tree, params } = &*func.borrow() {
                            println!("Calling function {op}");
                            // Create a new scope
                            let mut env = Environment {
                                up: Some(func_env.clone()),
                                ..Default::default()
                            };
                            let new_key = envs.insert(env);

                            for param in params.iter() {
                                let arg = eval(args.next().unwrap(), envs, key)?;
                                println!("Setting function env {param} = {arg:?}");
                                env_set(envs, new_key, param.clone(), arg);
                            }
    
                            eval(*tree.clone(), envs, new_key)
                        } else {
                            panic!("Attempted to call non-function variable as function")
                        }
                    } else {
                        panic!()
                    }
                } else if op == "fn" {
                    let params = eval(args.next().unwrap(), envs, key)?;
                    let ret_ty = eval(args.next().unwrap(), envs, key)?;
                    let block = args.next().unwrap();
                    if let Node::Table(params) = params {
                        let params: Vec<SmolStr> = params.keys().cloned().collect();
                        Ok(Node::Function { env: key, tree: Box::new(block), params })
                    } else {
                        panic!("Fn params must be table")
                    }
                } else if op == "print" {
                    let value = eval(args.next().unwrap(), envs, key)?;
                    println!("Print: {}", value);
                    Ok(value)
                } else if op == "struct" {
                    let structure = args.next().unwrap().into_table().unwrap();
                    let structure: Result<IndexMap<_, _>, Box<dyn Error>> =
                        structure.into_iter().map(|(k, v)| {
                            Ok((k, eval(v, envs, key)?))
                        }).collect();

                    Ok(Node::Type(Type::Struct(
                        structure?
                    )))
                } else if op == "+" {
                    let a = eval(args.next().unwrap(), envs, key)?;
                    let b = eval(args.next().unwrap(), envs, key)?;
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
                for i in 0..list.len() {
                    list[i] = eval(mem::replace(&mut list[i], Node::List(Vec::new())), envs, key)?;
                }
                Ok(Node::List(list))
            }
        },
        _ => todo!()
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
    let mut envs = SlotMap::with_key();
    let mut global_env = Environment::default();
    global_env.bindings.insert("Number".into(), Reference::new(Node::Type(Type::Primitive)));
    global_env.bindings.insert("Function".into(), Reference::new(Node::Type(Type::Primitive)));
    let global_env_key = envs.insert(global_env);
    println!("Result: {}", eval(tree, &mut envs, global_env_key).unwrap());
}
