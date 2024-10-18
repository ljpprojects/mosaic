use std::error::Error;
use std::fmt::Display;
use std::os::unix::prelude::FileExt;
use std::rc::Rc;
use std::string::ToString;
use crate::lexer::{LexError, StreamedLexer};
use crate::ptr_op_mut;
use crate::tokens::{Token};

pub const ADDITIVE_OPS: &[&str] = &["+", "-"];
pub const MULTIPLICATIVE_OPS: &[&str] = &["*", "/", "%"];
pub const EXPONENTIAL_OPS: &[&str] = &["^"];

#[derive(Debug)]
pub enum AstNode {
    NumberLiteral(f64),
    StringLiteral(String),
    Identifier(String),
    InfixOp(Rc<AstNode>, String, Rc<AstNode>),
    PrefixOp(String, Rc<AstNode>),
    PostfixOp(Rc<AstNode>, String),
    Path(Box<[String]>),
    Program(Box<[AstNode]>)
}

#[derive(Debug)]
pub enum ParseError {
    /// Expected: Token, Found: Token
    ExpectedToken(Token, Token),

    UnexpectedEOF,

    /// Found: Token
    InvalidToken(Token),

    LexError(LexError),

    InvalidNode(AstNode)
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedEOF => write!(f, "Unexpected end of file during parsing."),
            ParseError::InvalidToken(token) => write!(f, "Invalid token '{:?}'.", token),
            ParseError::ExpectedToken(token, expected) => write!(f, "Expected token '{expected:?}', got '{token:?}'"),
            ParseError::LexError(err) => write!(f, "Lex error: {:?}", err),
            ParseError::InvalidNode(node) => write!(f, "Invalid node: {:?}", node),
        }
    }
}

impl Error for ParseError {}

pub struct StreamedParser<R>
where R: FileExt {
    lexer: *mut StreamedLexer<R>
}

impl<R: FileExt> Clone for StreamedParser<R> {
    fn clone(&self) -> StreamedParser<R> {
        StreamedParser { lexer: self.lexer }
    }
}

impl<R: FileExt> Iterator for StreamedParser<R> {
    type Item = Result<AstNode, ParseError>;

    #[no_mangle]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_ast_node()
    }
}

impl<R: FileExt> StreamedParser<R> {
    pub fn new(lexer: *mut StreamedLexer<R>) -> Self {
        Self { lexer }
    }

    pub fn expect_chars<'a>(&mut self, chars: &'a &'a str) -> Result<&'a str, ParseError> {
        for char in chars.chars() {
            self.expect_char(&char)?;
        }

        Ok(chars.clone())
    }

    pub fn expect_char(&mut self, c: &char) -> Result<char, ParseError> {
        let tk = unsafe { (*self.lexer).peek_next_token() };

        let Some(tk) = tk else {
            return Err(ParseError::UnexpectedEOF);
        };

        let Ok(tk) = tk.map_err(|e| ParseError::LexError(e)) else {
            return Err(
                ParseError::UnexpectedEOF
            );
        };

        if let Token::Char(char, _) = tk {
            if char == *c {
                unsafe { (*self.lexer).next_token() };

                Ok(char)
            } else {
                Err(
                    ParseError::ExpectedToken(
                        Token::Char(c.to_owned(), tk.line_info()),
                        Token::Char(char, tk.line_info()),
                    )
                )
            }
        } else {
            Err(
                ParseError::ExpectedToken(
                    Token::Char(c.to_owned(), tk.line_info()),
                    tk
                )
            )
        }
    }

    #[no_mangle]
    pub fn parse_primary_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let token = match ptr_op_mut! (
            self.lexer => next_token
        )? {
            Ok(token) => token,
            Err(e) => return Some(Err(ParseError::LexError(e)))
        };

        match token {
            Token::Char(c, _) => {
                let Some(next) = self.next_ast_node() else {
                    return Some(Err(ParseError::UnexpectedEOF))
                };

                let Ok(next) = next else {
                    return Some(Err(next.err().unwrap()))
                };

                Some(Ok(AstNode::PrefixOp(c.to_string(), Rc::from(next))))
            }

            Token::String(s, _) => {
                Some(Ok(AstNode::StringLiteral(s)))
            }
            Token::Ident(i, _) => {
                Some(Ok(AstNode::Identifier(i)))
            }
            Token::Number(n, _) => {
                Some(Ok(AstNode::NumberLiteral(n)))
            }
        }
    }

    #[no_mangle]
    pub fn parse_multiplicative_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_primary_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e))
        };

        let Some(tk) = ptr_op_mut! (
            self.lexer => peek_next_token
        ) else {
            return Some(Ok(left))
        };

        let tk = match tk {
            Ok(tk) => tk,
            Err(e) => return Some(Err(ParseError::LexError(e)))
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left))
        };

        if MULTIPLICATIVE_OPS.contains(&op.to_string().as_str()) {
            ptr_op_mut! {
                self.lexer => next_token, unwrap, unwrap
            };

            let Some(right) = self.parse_multiplicative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                },

                Err(e) => return Some(Err(e))
            }
        }

        Some(Ok(left))
    }

    pub fn parse_path_expr(&mut self, left: AstNode) -> Option<Result<AstNode, ParseError>> {
        let AstNode::Identifier(begin) = left else { return Some(Ok(left)) };
        let mut path: Vec<String> = vec!(begin);

        while self.expect_chars(&"::").is_ok() {
            let Some(next) = self.parse_path_expr(AstNode::Path(path.clone().into_boxed_slice())) else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            let AstNode::Path(next) = (match next {
                Err(e) => return Some(Err(e)),
                Ok(ref o) => o
            }) else {
                return Some(Err(ParseError::InvalidNode(next.unwrap())))
            };

            path.extend_from_slice(next)
        }

        Some(Ok(AstNode::Path(path.into_boxed_slice())))
    }

    pub fn parse_additive_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_multiplicative_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let Some(tk) = ptr_op_mut! (
            self.lexer => peek_next_token
        ) else {
            return Some(Ok(left))
        };

        let Ok(tk) = tk else {
            return Some(Err(ParseError::LexError(tk.err().unwrap())))
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left))
        };

        if op == ':' {
            return self.parse_path_expr(left)
        }

        if ADDITIVE_OPS.contains(&op.to_string().as_str()) {
            ptr_op_mut! {
                self.lexer => next_token, unwrap, unwrap
            };

            let Some(right) = self.parse_additive_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                },

                Err(e) => return Some(Err(e))
            }
        }

        Some(Ok(left))
    }

    pub fn next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.parse_additive_expr()
    }
}