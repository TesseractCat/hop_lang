use std::mem;

use indexmap::IndexMap;
use logos::{Lexer, Logos, Span};
use smol_str::SmolStr;
use thiserror::Error;

use crate::ast::{Node, Reference, SpanNode};

#[derive(Error, Debug)]
pub enum ParseError {
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
    pub fn span(&self) -> Span {
        match self {
            Self::ExpectedList { span, .. } |
            Self::UnexpectedToken { span, .. } |
            Self::ExpectedSymbol { span, .. } |
            Self::Generic(span) => span.clone(),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Clone)]
#[logos(skip r"[ \t\r\n\f]+")] // Ignore whitespace
#[logos(skip r"//[^\r\n]*(\r\n|\n)?")] // Ignore comments
pub enum Token {
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
    
    #[token("'")]
    Quote,

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
    #[regex(r#":[a-zA-Z\-\/+_=]+[a-zA-Z\-\/+_=><]*"#, |lex| {
        let m = lex.slice();
        SmolStr::from(&m[1..m.len()])
    })]
    Keyword(SmolStr),

    // Sugar
    #[regex(r#"\.\("#)]
    Call,

    #[token(".")]
    Deref,
}

// foo.(1 2 3) -> (call foo (1 2 3))
pub fn parse_call(lexer: &mut Lexer<'_, Token>, lhs: SpanNode) -> Result<SpanNode, ParseError> {
    let (l, _) = parse_list(lexer, &[Token::ListClose])?;
    let l = l.node.into_list().map_err(|_| ParseError::Generic(lexer.span()))?;
    let mut res = vec![Node::new_symbol(lexer.span(), "call".into()), lhs];
    res.append(&mut l.borrow_mut());
    Ok(Node::new_list(lexer.span(), Reference::new(res)))
}
// foo.bar.baz -> (get (get foo bar) baz)
pub fn parse_deref(lexer: &mut Lexer<'_, Token>, lhs: SpanNode) -> Result<SpanNode, ParseError> {
    let token = lexer.next().ok_or(ParseError::Generic(lexer.span()))?.unwrap();
    match token {
        Token::Symbol(rhs) => {
            Ok(Node::new_list(
                lexer.span(), Reference::new(vec![Node::new_symbol(lexer.span(), "get".into()), lhs, Node::new_keyword(lexer.span(), rhs)])
            ))
        },
        _ => Err(ParseError::ExpectedSymbol { got: token, span: lexer.span() })
    }
}
// [a: "hi", b: 2]
pub fn parse_table(lexer: &mut Lexer<'_, Token>) -> Result<SpanNode, ParseError> {
    let mut table: IndexMap<SpanNode, SpanNode> = IndexMap::new();
    let mut want_key = true;
    let start = lexer.span().start;

    let mut key: Vec<SpanNode> = Vec::new();
    let mut value: Vec<SpanNode> = Vec::new();

    loop {
        if want_key {
            let (list, stop_token) = parse_list(lexer, &[Token::Colon, Token::TableClose])?;
            key = mem::take(&mut *list.into_list().unwrap().borrow_mut());
            want_key = !want_key;
            if stop_token == Token::TableClose {
                break;
            }
        } else {
            let (list, stop_token) = parse_list(lexer, &[Token::Comma, Token::TableClose])?;
            value = mem::take(&mut *list.into_list().unwrap().borrow_mut());
            table.insert(
                if key.len() == 1 {
                    let key = mem::take(&mut key).into_iter().next().unwrap();
                    let key_tag = key.tag.clone();
                    match key.into_symbol() {
                        Ok(key_symbol) => Node::new_keyword(key_tag, key_symbol),
                        Err(key) => key,
                    }
                } else {
                    Node::new_list(
                        lexer.span(), Reference::new(mem::take(&mut key))
                    )
                },
                if value.len() == 1 {
                    mem::take(&mut value).into_iter().next().unwrap()
                } else {
                    Node::new_list(
                        lexer.span(), Reference::new(mem::take(&mut value))
                    )
                }
            );
            want_key = !want_key;
            if stop_token == Token::TableClose {
                break;
            }
        }
    }

    Ok(Node::new_table(start..lexer.span().end, Reference::new(table)))
}
// (a 123 false)
pub fn parse_list(lexer: &mut Lexer<'_, Token>, stop_tokens: &[Token]) -> Result<(SpanNode, Token), ParseError> {
    let mut res: Vec<SpanNode> = Vec::new();
    let start = lexer.span().start;

    let mut quoting = false;
    let mut quote_span = Span::default();
    while let Some(token) = lexer.next() {
        let node = match token.map_err(|_| ParseError::Generic(lexer.span()))? {
            Token::ListOpen => Some(parse_list(lexer, &[Token::ListClose])?.0),
            Token::BlockOpen => Some(parse_block(lexer)?),
            Token::TableOpen => Some(parse_table(lexer)?),

            Token::Quote => { quoting = true; quote_span = lexer.span(); None },

            Token::Bool(bool) => Some(Node::new_bool(lexer.span(), bool)),
            Token::Number(num) => Some(Node::new_number(lexer.span(), num)),
            Token::String(str) => Some(Node::new_string(lexer.span(), str)),
            Token::Symbol(str) => Some(Node::new_symbol(lexer.span(), str)),
            Token::Keyword(str) => Some(Node::new_keyword(lexer.span(), str)),

            Token::Call => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = res.remove(res.len() - 1);
                Some(parse_call(lexer, lhs)?)
            },
            Token::Deref => {
                if res.len() == 0 { return Err(ParseError::Generic(lexer.span())); }
                let lhs = res.remove(res.len() - 1);
                Some(parse_deref(lexer, lhs)?)
            },
            token => {
                for stop_token in stop_tokens {
                    if token == *stop_token {
                        return Ok((Node::new_list(start..lexer.span().end, Reference::new(res)), stop_token.clone()));
                    }
                }
                return Err(ParseError::UnexpectedToken { got: token, span: lexer.span() })
            }
        };
        if let Some(node) = node {
            if quoting {
                res.push(Node::new_list(node.tag.clone(), Reference::new(vec![
                    Node::new_symbol(quote_span.clone(), "quote".into()),
                    node
                ])));
                quoting = false;
            } else {
                res.push(node);
            }
        }
    }
    panic!("EOF while reading list")
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
pub fn parse_block(lexer: &mut Lexer<'_, Token>) -> Result<SpanNode, ParseError> {
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

            Token::ListOpen => list.push(parse_list(lexer, &[Token::ListClose])?.0),
            Token::TableOpen => list.push(parse_table(lexer)?),
            Token::BlockOpen => list.push(parse_block(lexer)?),

            Token::Bool(bool) => list.push(Node::new_bool(lexer.span(), bool)),
            Token::Number(num) => list.push(Node::new_number(lexer.span(), num)),
            Token::String(str) => list.push(Node::new_string(lexer.span(), str)),
            Token::Symbol(str) => list.push(Node::new_symbol(lexer.span(), str)),
            Token::Keyword(str) => list.push(Node::new_keyword(lexer.span(), str)),

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