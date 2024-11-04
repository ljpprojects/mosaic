#![forbid(unsafe_code)]

use crate::lexer::{LexError, StreamedLexer};
use crate::states::{ParserState, WithState};
use crate::tokens::{LineInfo, Token};
use std::error::Error;
use std::fmt::Display;
use std::rc::Rc;
use std::string::ToString;

pub const ADDITIVE_OPS: &[&str] = &["+", "-"];
pub const MULTIPLICATIVE_OPS: &[&str] = &["*", "/", "%"];
pub const EXPONENTIAL_OPS: &[&str] = &["^"];
pub const PREFIX_OPS: &[&str] = &["!", "-", "+"];

#[derive(Debug)]
pub enum ParseType {
    IdentType(String),
    SpecificNumberType(f64),
    ArrayType {
        element_type: Rc<ParseType>,
        length: Option<u32>,
    },
    PathType(Box<[String]>),
}

#[derive(Debug)]
pub enum ParseBlock {
    Plain(Box<[AstNode]>)
}

#[derive(Debug)]
pub enum AstNode {
    // --- EXPRESSIONS --- //
    NumberLiteral(f64),
    StringLiteral(String),
    ArrayLiteral(Box<[AstNode]>),
    Identifier(String),
    InfixOp(Rc<AstNode>, String, Rc<AstNode>),
    PrefixOp(String, Rc<AstNode>),
    PostfixOp(Rc<AstNode>, String),
    Path(Box<[String]>),
    MemberExpr(Box<[String]>),
    CallExpr {
        callee: Rc<AstNode>,
        args: Box<[AstNode]>,
    },
    AsExpr(Rc<AstNode>, ParseType),

    // --- Statements --- //
    DefStmt {
        name: String,
        def_type: ParseType,
        value: Rc<AstNode>,
    },

    /// self.0 is always an AstNode::Path
    UseStmt(Rc<AstNode>),

    // --- SPECIAL --- //
    Program(Box<[AstNode]>),
}

#[derive(Debug)]
pub enum ParseError {
    /// Expected: Token, Found: Token
    ExpectedToken(Token, Token),

    UnexpectedEOF,

    LexError(LexError),

    InvalidNode(AstNode),

    InvalidToken(Token),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedEOF => write!(f, "Unexpected end of file during parsing."),
            ParseError::ExpectedToken(token, expected) => {
                write!(f, "Expected token '{expected:?}', got '{token:?}'")
            }
            ParseError::LexError(err) => write!(f, "Lex error: {err:?}"),
            ParseError::InvalidNode(node) => write!(f, "Invalid node: {node:?}"),
            ParseError::InvalidToken(token) => write!(f, "Invalid token: {token:?}"),
        }
    }
}

impl Error for ParseError {}

pub struct StreamedParser {
    lexer: StreamedLexer,
}

impl WithState for StreamedParser {
    type ToState = ParserState;

    fn from_state(state: Self::ToState) -> Self {
        Self::new(StreamedLexer::from_state(state.lexer_state))
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        self.lexer = StreamedLexer::from_state(state.lexer_state)
    }

    fn state(&self) -> Self::ToState {
        ParserState::new(self.lexer.state())
    }
}

impl Clone for StreamedParser {
    fn clone(&self) -> StreamedParser {
        StreamedParser {
            lexer: self.lexer.clone(),
        }
    }
}

impl Iterator for StreamedParser {
    type Item = Result<AstNode, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_ast_node()
    }
}

impl StreamedParser {
    pub fn new(lexer: StreamedLexer) -> Self {
        Self { lexer }
    }

    pub fn expect_ident<'b>(
        &mut self,
        chars: &'b &'b str,
        mutate: bool,
    ) -> Result<String, ParseError> {
        let tk = self.lexer.peek_next_token();

        match tk {
            None => Err(ParseError::UnexpectedEOF),
            Some(Err(e)) => Err(ParseError::LexError(e)),
            Some(Ok(Token::Ident(ref c, _))) => {
                if c.as_str() == *chars {
                    if mutate {
                        self.lexer.next_token();
                    }

                    Ok(c.clone())
                } else {
                    Err(ParseError::ExpectedToken(
                        Token::Ident(chars.to_string(), LineInfo::default()),
                        tk.clone().unwrap().unwrap(),
                    ))
                }
            }
            _ => Err(ParseError::ExpectedToken(
                Token::Ident(chars.to_string(), LineInfo::default()),
                tk.unwrap().unwrap(),
            )),
        }
    }

    pub fn expect_chars<'b>(
        &mut self,
        chars: &'b &'b str,
        mutate: bool,
    ) -> Result<&'b str, ParseError> {
        for char in chars.chars() {
            self.expect_char(&char, mutate)?;
        }

        Ok(chars)
    }

    pub fn expect_char(&mut self, c: &char, m: bool) -> Result<char, ParseError> {
        let tk = self.lexer.peek_next_token();

        let Some(tk) = tk else {
            return Err(ParseError::UnexpectedEOF);
        };

        let Ok(tk) = tk.map_err(|e| ParseError::LexError(e)) else {
            return Err(ParseError::UnexpectedEOF);
        };

        if let Token::Char(char, _) = tk {
            if char == *c {
                if m {
                    self.lexer.next_token();
                }

                Ok(char)
            } else {
                Err(ParseError::ExpectedToken(
                    Token::Char(c.to_owned(), tk.line_info()),
                    Token::Char(char, tk.line_info()),
                ))
            }
        } else {
            Err(ParseError::ExpectedToken(
                Token::Char(c.to_owned(), tk.line_info()),
                tk,
            ))
        }
    }

    fn parse_num_type(&mut self) -> Result<ParseType, ParseError> {
        let t = match self.lexer.next_token() {
            Some(Ok(Token::Number(t, _))) => t,
            Some(Ok(tk)) => panic!("Invalid token for type parsing: {tk:?}"),
            Some(Err(e)) => return Err(ParseError::LexError(e)),
            None => return Err(ParseError::UnexpectedEOF),
        };

        Ok(ParseType::SpecificNumberType(t))
    }

    fn parse_ident_type(&mut self) -> Result<ParseType, ParseError> {
        let t = match self.lexer.peek_next_token() {
            Some(Ok(Token::Ident(t, _))) => t,
            Some(Ok(_tk)) => return self.parse_num_type(),
            Some(Err(e)) => return Err(ParseError::LexError(e)),
            None => return Err(ParseError::UnexpectedEOF),
        };

        self.lexer.next_token();

        Ok(ParseType::IdentType(t))
    }

    fn parse_array_type(&mut self) -> Result<ParseType, ParseError> {
        self.expect_chars(&"[", true)?;

        let element_type = self.parse_type()?;

        let length = match self.lexer.peek_next_token() {
            Some(Ok(Token::Number(n, _))) => {
                self.lexer.next_token();

                n as u32
            }
            Some(Ok(_)) => {
                self.expect_chars(&"]", true)?;
                
                return Ok(ParseType::ArrayType {
                    element_type: Rc::from(element_type),
                    length: None,
                })
            }
            Some(Err(e)) => return Err(ParseError::LexError(e)),
            None => {
                return Ok(ParseType::ArrayType {
                    element_type: Rc::from(element_type),
                    length: None,
                })
            }
        };

        self.expect_chars(&"]", true)?;

        Ok(ParseType::ArrayType {
            element_type: Rc::from(element_type),
            length: Some(length),
        })
    }

    fn parse_type(&mut self) -> Result<ParseType, ParseError> {
        if let Ok(_) = self.expect_chars(&"[", false) {
            return self.parse_array_type();
        }

        let mut left = match self.parse_ident_type() {
            Ok(t) => t,
            Err(e) => return Err(e),
        };

        if let Ok(_) = self.expect_chars(&"::", false) {
            let ParseType::IdentType(left_tname) = left else {
                return Ok(left);
            };

            let right = match self.parse_path_expr(Some(AstNode::Identifier(left_tname.clone()))) {
                Some(Ok(AstNode::Path(p))) => p,
                Some(Ok(_)) => unreachable!(),
                Some(Err(e)) => return Err(e),
                None => return Err(ParseError::UnexpectedEOF),
            };

            left = ParseType::PathType(Box::from(&*right))
        };

        Ok(left)
    }

    pub fn parse_list(&mut self, left: Option<AstNode>) -> Result<Vec<AstNode>, ParseError> {
        let begin = match (|| {
            let Some(left) = left else {
                let tk = self.next_ast_node();

                return Ok(match tk {
                    Some(Ok(node)) => node,
                    Some(Err(e)) => return Err(e),
                    None => return Err(ParseError::UnexpectedEOF),
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(e) => return Err(e),
        };

        let mut items: Vec<AstNode> = vec![begin];

        while self.expect_chars(&",", true).is_ok() {
            let next = self.next_ast_node();

            let next = match next {
                Some(Ok(node)) => node,
                Some(Err(e)) => return Err(e),
                _ => break,
            };

            items.push(next)
        }

        Ok(items)
    }
    
    pub fn parse_array_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let args = match self.parse_list(None) {
            Ok(args) => args,
            Err(e) => return Some(Err(e)),
        };

        match self.expect_chars(&"]", true) {
            Ok(_) => Some(Ok(AstNode::ArrayLiteral(args.into_boxed_slice()))),
            Err(e) => Some(Err(e)),
        }
    }

    pub fn parse_primary_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let token = match self.lexer.next_token()? {
            Ok(token) => token,
            Err(e) => return Some(Err(ParseError::LexError(e))),
        };

        match token {
            Token::Char(c, line_info) => {
                if c == '[' {
                    return self.parse_array_expr()
                }
                
                let Some(next) = self.next_ast_node() else {
                    return Some(Err(ParseError::UnexpectedEOF));
                };

                let Ok(next) = next else {
                    return Some(Err(next.err().unwrap()));
                };

                if PREFIX_OPS.contains(&c.to_string().as_str()) {
                    return Some(Ok(AstNode::PrefixOp(c.to_string(), Rc::from(next))));
                } else if c == '(' {
                    return match self.expect_char(&')', true) {
                        Err(e) => Some(Err(e)),
                        Ok(_) => Some(Ok(next)),
                    };
                }

                Some(Err(ParseError::InvalidToken(Token::Char(c, line_info))))
            }

            Token::String(s, _) => Some(Ok(AstNode::StringLiteral(s))),
            Token::Ident(i, _) => self.parse_call_expr(AstNode::Identifier(i)),
            Token::Number(n, _) => Some(Ok(AstNode::NumberLiteral(n))),
        }
    }

    pub fn parse_call_expr(&mut self, caller: AstNode) -> Option<Result<AstNode, ParseError>> {
        if let Ok(_) = self.expect_chars(&"(", true) {
            let args = match self.parse_list(None) {
                Ok(args) => args,
                Err(e) => return Some(Err(e)),
            };

            match self.expect_chars(&")", true) {
                Ok(_) => Some(Ok(AstNode::CallExpr {
                    callee: Rc::from(caller),
                    args: args.into_boxed_slice(),
                })),
                Err(e) => Some(Err(e)),
            }
        } else {
            Some(Ok(caller))
        }
    }

    pub fn parse_path_expr(
        &mut self,
        left: Option<AstNode>,
    ) -> Option<Result<AstNode, ParseError>> {
        let begin = match (|| {
            let Some(AstNode::Identifier(left)) = left else {
                let tk = self.lexer.next_token();

                return Ok(match tk {
                    Some(Ok(Token::Ident(begin, _))) => begin,
                    Some(Ok(tk)) => {
                        return Err(ParseError::ExpectedToken(
                            Token::Ident("".to_string(), LineInfo::default()),
                            tk,
                        ))
                    }
                    Some(Err(e)) => return Err(ParseError::LexError(e)),
                    None => return Err(ParseError::UnexpectedEOF),
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(e) => return Some(Err(e)),
        };

        let mut path: Vec<String> = vec![begin];

        while self.expect_chars(&"::", true).is_ok() {
            let next = self.lexer.next_token();

            let next = match next {
                Some(Ok(Token::Ident(begin, _))) => begin,
                Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
                _ => break,
            };

            path.push(next)
        }

        self.parse_call_expr(AstNode::Path(path.into_boxed_slice()))
    }

    pub fn parse_member_expr(
        &mut self,
        left: Option<AstNode>,
    ) -> Option<Result<AstNode, ParseError>> {
        let begin = match (|| {
            let Some(AstNode::Identifier(left)) = left else {
                let tk = self.lexer.next_token();

                return Ok(match tk {
                    Some(Ok(Token::Ident(begin, _))) => begin,
                    Some(Ok(tk)) => {
                        return Err(ParseError::ExpectedToken(
                            Token::Ident("".to_string(), LineInfo::default()),
                            tk,
                        ))
                    }
                    Some(Err(e)) => return Err(ParseError::LexError(e)),
                    None => return Err(ParseError::UnexpectedEOF),
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(e) => return Some(Err(e)),
        };

        let mut path: Vec<String> = vec![begin];

        while self.expect_chars(&".", true).is_ok() {
            let next = self.lexer.next_token();

            let next = match next {
                Some(Ok(Token::Ident(begin, _))) => begin,
                Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
                _ => break,
            };

            path.push(next)
        }

        self.parse_call_expr(AstNode::MemberExpr(path.into_boxed_slice()))
    }

    pub fn parse_cast_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_primary_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let Some(tk) = self.lexer.peek_next_token() else {
            return Some(Ok(left));
        };

        match tk {
            Err(e) => return Some(Err(ParseError::LexError(e))),
            _ => (),
        };

        if let Ok(_) = self.expect_ident(&"as", true) {
            let right = match self.parse_type() {
                Ok(t) => t,
                Err(e) => return Some(Err(e)),
            };

            left = AstNode::AsExpr(Rc::from(left), right)
        }

        Some(Ok(left))
    }

    pub fn parse_exponential_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_cast_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let Some(tk) = self.lexer.peek_next_token() else {
            return Some(Ok(left));
        };

        let tk = match tk {
            Ok(tk) => tk,
            Err(e) => return Some(Err(ParseError::LexError(e))),
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if op == '.' {
            return self.parse_member_expr(Some(left));
        } else if op == ':' {
            return self.parse_path_expr(Some(left));
        } else if EXPONENTIAL_OPS.contains(&op.to_string().as_str()) {
            self.lexer.next_token().unwrap().unwrap();

            let Some(right) = self.parse_exponential_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_multiplicative_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_exponential_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let Some(tk) = self.lexer.peek_next_token() else {
            return Some(Ok(left));
        };

        let tk = match tk {
            Ok(tk) => tk,
            Err(e) => return Some(Err(ParseError::LexError(e))),
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if MULTIPLICATIVE_OPS.contains(&op.to_string().as_str()) {
            self.lexer.next_token().unwrap().unwrap();

            let Some(right) = self.parse_multiplicative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_additive_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_multiplicative_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let Some(tk) = self.lexer.peek_next_token() else {
            return Some(Ok(left));
        };

        let Ok(tk) = tk else {
            return Some(Err(ParseError::LexError(tk.err().unwrap())));
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if ADDITIVE_OPS.contains(&op.to_string().as_str()) {
            self.lexer.next_token().unwrap().unwrap();

            let Some(right) = self.parse_additive_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_comparative_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_additive_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        if let Ok(op) = self.expect_chars(&"==", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"!=", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"||", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"&&", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_def_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"def", true).unwrap();

        let def_type = match self.parse_type() {
            Ok(def_type) => def_type,
            Err(e) => return Some(Err(e)),
        };

        let name = match self.lexer.next_token() {
            None => return Some(Err(ParseError::UnexpectedEOF)),
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    Token::Ident("NAME".to_string(), LineInfo::default()),
                    tk,
                )))
            }
        };

        self.expect_chars(&"->", true).unwrap();

        let value = match self.next_ast_node() {
            None => return Some(Err(ParseError::UnexpectedEOF)),
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
        };

        Some(Ok(AstNode::DefStmt {
            name,
            def_type,
            value: Rc::from(value),
        }))
    }
    
    pub fn parse_use_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"use", true).unwrap();
        
        let path = match self.parse_path_expr(None) {
            Some(Ok(AstNode::Path(path))) => path,
            Some(Ok(_)) => unreachable!(),
            Some(Err(e)) => return Some(Err(e)),
            None => return Some(Err(ParseError::UnexpectedEOF)),
        };
        
        Some(Ok(AstNode::UseStmt(Rc::from(AstNode::Path(path)))))
    }

    pub fn next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        if let Some(Ok(Token::Ident(ident, _))) = self.lexer.peek_next_token() {
            match ident.as_str() {
                "def" => self.parse_def_stmt(),
                "use" => self.parse_use_stmt(),
                _ => self.parse_comparative_expr(),
            }
        } else {
            self.parse_comparative_expr()
        }
    }

    pub fn peek_next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        let prev_state = self.state();

        let node = self.next_ast_node();

        self.reset_to_state(prev_state);

        node
    }
}
