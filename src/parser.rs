use crate::lexer::{LexError, StreamedLexer};
use crate::states::{ParserState, WithState};
use crate::tokens::{LineInfo, Token};
use crate::utils::{Indirection, OneOf};
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;
use std::string::ToString;
use cranelift_codegen::CompileError;
use crate::errors::CompilationError;

pub const ADDITIVE_OPS: &[&str] = &["+", "-"];
pub const MULTIPLICATIVE_OPS: &[&str] = &["*", "/", "%"];
pub const EXPONENTIAL_OPS: &[&str] = &["^"];
pub const PREFIX_OPS: &[&str] = &["!", "-", "+", "*", "&"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Modifier {
    Export,

    /// Tell the compiler to automatically free the returned value of a function when
    /// a 'return' statement is compiled.
    /// To manually free before a return statement is compiled, use the 'autofree' statement.
    AutoFree,
}

#[macro_export]
macro_rules! modifier {
    ($s: literal) => {
        match crate::parser::Modifier::from_str($s) {
            Err(_) => compile_error!($s),
            Ok(m) => m,
        }
    };
}

impl FromStr for Modifier {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "export" => Ok(Modifier::Export),
            "autofree" | "auto_free" => Ok(Modifier::AutoFree),
            m => Err(format!("Invalid modifier {m}"))
        }
    }
}

#[derive(Clone)]
pub enum ParseType {
    IdentType(String),
    ArrayType {
        element_type: Indirection<ParseType>,
        length: usize,
    },
    PointerType(Indirection<ParseType>),
    FatPointerType(Indirection<ParseType>, u32),
    TerminatedSlice(Indirection<ParseType>, Indirection<AstNode>),
}

impl Debug for ParseType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for ParseType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseType::IdentType(t) => write!(f, "{t}"),
            ParseType::ArrayType {
                element_type,
                length,
            } => write!(f, "[{element_type} {length}]"),
            ParseType::PointerType(p) => write!(f, "*{p}"),
            ParseType::FatPointerType(t, l) => write!(f, "*{l}[{t}]"),
            ParseType::TerminatedSlice(t, e) => write!(f, "*:{e}[{t}]"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParseBlock {
    Plain(Box<[AstNode]>),
}

impl Display for ParseBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseBlock::Plain(b) => write!(
                f,
                "{}",
                b.iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeBound {
    Iterator(Indirection<ParseType>),
    Not(Indirection<TypeBound>),
    Compound(Box<[TypeBound]>),
}

impl Display for TypeBound {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeBound::Iterator(i) => write!(f, "iter[{i}]"),
            TypeBound::Not(b) => write!(f, "!{b}"),
            TypeBound::Compound(bounds) => write!(f, "{B}", B = bounds.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(" + "))
        }
    }
}

#[derive(Debug, Clone)]
pub enum AstNode {
    // --- EXPRESSIONS --- //
    NumberLiteral(LineInfo, f64),
    ByteLiteral(LineInfo, u8),
    StringLiteral(LineInfo, String),
    ArrayLiteral(LineInfo, Box<[AstNode]>),
    BooleanLiteral(LineInfo, bool),
    NullLiteral(LineInfo),
    Identifier(LineInfo, String),
    InfixOp(LineInfo, Rc<AstNode>, String, Rc<AstNode>),
    PrefixOp(LineInfo, String, Indirection<AstNode>),
    PostfixOp(LineInfo, Rc<AstNode>, String),
    Path(LineInfo, Box<[String]>),
    MemberExpr(LineInfo, Box<[String]>),
    IdxAccess(LineInfo, Indirection<AstNode>, Indirection<AstNode>),
    CallExpr {
        line_info: LineInfo,
        callee: Rc<AstNode>,
        args: Box<[AstNode]>,
    },
    AsExpr(LineInfo, Rc<AstNode>, ParseType),
    IfExpr {
        line_info: LineInfo,
        cond: Rc<AstNode>,
        block: ParseBlock,
        else_clause: ParseBlock,
    },
    ForInExpr {
        line_info: LineInfo,
        var: String,
        of: Indirection<AstNode>,
        block: ParseBlock,
    },
    FnExpr {
        name: String,
        ret_type: ParseType,

        /// Box<\[(name, type, default)\]>
        args: Box<[(LineInfo, String, ParseType, Option<AstNode>)]>,

        type_generics: HashMap<String, Option<TypeBound>>,
        code: ParseBlock,
        modifiers: Box<[Modifier]>
    },

    // --- Statements --- //
    DefStmt {
        name_info: LineInfo,
        name: String,
        def_type: ParseType,
        value: Rc<AstNode>,
    },

    /// self.0 is always an AstNode::Path
    IncludeStmt(LineInfo, Box<[String]>),

    IfStmt {
        line_info: LineInfo,
        cond: Rc<AstNode>,
        block: ParseBlock,
    },

    ExternFn {
        line_info: LineInfo,
        name: String,
        ret_type: ParseType,

        /// Box<\[(name, type, default)\]>
        args: Box<[(LineInfo, String, ParseType, Option<AstNode>)]>,
    },
    
    ExternDef {
        name: String,
        def_type: ParseType
    },

    ReturnStmt(Indirection<AstNode>),

    // --- SPECIAL --- //
    Program(Box<[AstNode]>),
}

impl Display for AstNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::NumberLiteral(n) => write!(f, "{n}"),
            AstNode::StringLiteral(s) => write!(f, "\"{s}\""),
            AstNode::ArrayLiteral(arr) => write!(f, "{arr:?}"),
            AstNode::BooleanLiteral(b) => write!(f, "{b}"),
            AstNode::NullLiteral => write!(f, "null"),
            AstNode::Identifier(i) => write!(f, "{i}"),
            AstNode::InfixOp(l, o, r) => write!(f, "{l} {o} {r}"),
            AstNode::PrefixOp(o, v) => write!(f, "{o}({v})"),
            AstNode::PostfixOp(v, o) => write!(f, "({v}){o}"),
            AstNode::Path(p) => write!(f, "{}", p.join("::")),
            AstNode::MemberExpr(p) => write!(f, "{}", p.join(".")),
            AstNode::IdxAccess(v, i) => write!(f, "{v}[{i}]"),
            AstNode::CallExpr { args, callee } => write!(
                f,
                "({callee})({})",
                args.iter()
                    .map(|n| format!("{n}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            AstNode::AsExpr(v, t) => write!(f, "({v}) as {t}"),
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
            } => write!(f, "if ({cond}) {{\n{block}}} else {{\n{else_clause}}}"),
            AstNode::FnExpr {
                name,
                ret_type,
                args,
                ..
            } => write!(f, "fn {name}({args:?}) -> {ret_type} {{ ... }}"),
            AstNode::DefStmt {
                name,
                def_type,
                value,
            } => write!(f, "def {def_type} {name} -> {value}"),
            AstNode::IncludeStmt(p) => write!(f, "include {P}", P = p.join("::")),
            AstNode::IfStmt { cond, block } => write!(f, "if ({cond}) {{\n{block}\n}}"),
            AstNode::ExternFn {
                name,
                ret_type,
                args,
            } => write!(f, "extern fn {name}({args:?}) -> {ret_type}"),
            AstNode::ExternDef {
                name,
                def_type,
            } => write!(f, "extern def {def_type} {name}"),
            AstNode::Program(p) => write!(
                f,
                "{}",
                p.iter()
                    .map(|n| format!("{n}"))
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
            AstNode::ReturnStmt(v) => write!(f, "return {v}"),
            AstNode::ForInExpr { var, of, block } => write!(f, "for {var} in {of} {{\n{block}\n}}"),
            AstNode::ByteLiteral(b) => write!(f, "'{C}'", C = *b as char)
        }
    }
}

type ParseError = CompilationError;

#[derive(Debug, PartialEq)]
pub struct StreamedParser {
    pub(crate) lexer: StreamedLexer,
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
    pub fn iter(&self) -> impl Iterator<Item = Result<AstNode, ParseError>> {
        let iter = self.clone().into_iter();

        iter.collect::<Vec<_>>().into_iter()
    }

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
            None => Err(ParseError::UnexpectedEOF(Token::Ident(
                chars.to_string(),
                LineInfo::default(),
            ))),
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
            return Err(ParseError::UnexpectedEOF(Token::Char(
                *c,
                LineInfo::default(),
            )));
        };

        let Ok(tk) = tk.map_err(ParseError::LexError) else {
            return Err(ParseError::UnexpectedEOF(Token::Char(
                *c,
                LineInfo::default(),
            )));
        };

        if let Token::Char(char, _) = tk {
            if char == *c {
                if m {
                    self.lexer.next_token();
                }

                Ok(char)
            } else {
                Err(ParseError::ExpectedToken(
                    Token::Char(char, tk.line_info()),
                    Token::Char(c.to_owned(), tk.line_info()),
                ))
            }
        } else {
            Err(ParseError::ExpectedToken(
                Token::Char(c.to_owned(), tk.line_info()),
                tk,
            ))
        }
    }

    fn parse_ident_type(&mut self) -> Result<ParseType, ParseError> {
        let t = match self.lexer.peek_next_token() {
            Some(Ok(Token::Ident(t, _))) => t,
            Some(Ok(tk)) => return Err(ParseError::InvalidToken(tk)),
            Some(Err(e)) => return Err(ParseError::LexError(e)),
            None => {
                return Err(ParseError::UnexpectedEOF(Token::Ident(
                    "TYPE".to_string(),
                    LineInfo::default(),
                )))
            }
        };

        self.lexer.next_token();

        Ok(ParseType::IdentType(t))
    }

    fn parse_type(&mut self) -> Result<ParseType, ParseError> {
        if self.expect_chars(&"*", true).is_ok() {
            // parse terminated slice
            if self.expect_chars(&":", true).is_ok() {
                let term = match self.lexer.next_token() {
                    None => {
                        return Err(ParseError::UnexpectedEOF(Token::Number(
                            1f64,
                            LineInfo::default(),
                        )))
                    }
                    Some(Ok(node)) => node,
                    Some(Err(e)) => return Err(ParseError::LexError(e)),
                };

                let term = match term {
                    Token::String(s, _) => AstNode::StringLiteral(s),
                    Token::Number(n, _) => AstNode::NumberLiteral(n),
                    _ => unimplemented!(),
                };

                self.expect_chars(&"[", true)?;

                let left = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Err(e),
                };

                self.expect_chars(&"]", true)?;

                return Ok(ParseType::TerminatedSlice(
                    Indirection::new(left),
                    Indirection::new(term),
                ));
            }

            // parse fat pointer
            if let Some(Ok(Token::Number(l, _))) = self.lexer.peek_next_token() {
                self.lexer.next_token();

                self.expect_chars(&"[", true)?;

                let left = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Err(e),
                };

                self.expect_chars(&"]", true)?;

                return Ok(ParseType::FatPointerType(Indirection::new(left), l as u32));
            }

            let left = match self.parse_type() {
                Ok(t) => t,
                Err(e) => return Err(e),
            };

            return Ok(ParseType::PointerType(Indirection::new(left)));
        }

        let left = match self.parse_ident_type() {
            Ok(t) => t,
            Err(e) => return Err(e),
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
                    None => {
                        return Err(ParseError::UnexpectedEOF(Token::Ident(
                            "ANY".to_string(),
                            LineInfo::default(),
                        )))
                    }
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(ParseError::UnexpectedEOF(_)) => return Ok(vec![]),
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

    pub fn parse_tg_bound(&mut self) -> Result<TypeBound, ParseError> {
        let mut left = match self.lexer.next_token() {
            None => return Err(ParseError::UnexpectedEOF(Token::Debug("TG_BOUND".into()))),
            Some(Err(e)) => return Err(ParseError::LexError(e)),
            Some(Ok(Token::Ident(i, _))) if i == "iter".to_string() => {
                self.expect_chars(&"[", true)?;

                let iterate_over = self.parse_type()?;

                self.expect_chars(&"]", true)?;

                TypeBound::Iterator(Indirection::new(iterate_over))
            },
            Some(Ok(Token::Char(c, _))) if c == '!' => TypeBound::Not(Indirection::new(self.parse_tg_bound()?)),
            Some(Ok(t)) => return Err(ParseError::InvalidToken(t))
        };

        while self.expect_chars(&"+", true).is_ok() {
            let right = self.parse_tg_bound()?;

            match right {
                TypeBound::Compound(b) => left = TypeBound::Compound([&[left], b.as_ref()].concat().into_boxed_slice()),
                b => left = b
            }
        }

        Ok(left)
    }

    pub fn parse_tg_list(&mut self) -> Result<HashMap<String, Option<TypeBound>>, ParseError> {
        self.expect_chars(&"<", true)?;

        if self.expect_chars(&">", true).is_ok() {
            return Ok(Default::default());
        }

        let mut args: HashMap<String, Option<TypeBound>> = Default::default();
        let mut is_first = true;

        while self.expect_chars(&",", true).is_ok() || is_first {
            is_first = false;

            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => {
                    return Err(ParseError::ExpectedToken(
                        Token::Ident("TG_NAME".to_string(), LineInfo::default()),
                        tk,
                    ))
                }
                Some(Err(e)) => return Err(ParseError::LexError(e)),
                None => {
                    return Err(ParseError::UnexpectedEOF(Token::Ident(
                        "PARAM_NAME".to_string(),
                        LineInfo::default(),
                    )))
                }
            };

            if self.expect_chars(&":", true).is_ok() {
                args.insert(name, Some(self.parse_tg_bound()?));
            } else {
                args.insert(name, None);
            }
        }

        self.expect_chars(&">", true)?;

        Ok(args)
    }

    pub fn parse_args_list(
        &mut self,
    ) -> Result<Vec<(String, ParseType, Option<AstNode>)>, ParseError> {
        self.expect_chars(&"(", true)?;

        if self.expect_chars(&")", true).is_ok() {
            return Ok(vec![]);
        }

        let mut args: Vec<(String, ParseType, Option<AstNode>)> = vec![];
        let mut is_first = true;

        while self.expect_chars(&",", true).is_ok() || is_first {
            is_first = false;

            let t = self.parse_type()?;

            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => {
                    return Err(ParseError::ExpectedToken(
                        Token::Ident("PARAM_NAME".to_string(), LineInfo::default()),
                        tk,
                    ))
                }
                Some(Err(e)) => return Err(ParseError::LexError(e)),
                None => {
                    return Err(ParseError::UnexpectedEOF(Token::Ident(
                        "PARAM_NAME".to_string(),
                        LineInfo::default(),
                    )))
                }
            };

            if self.expect_chars(&"=", true).is_ok() {
                let default = match self.next_ast_node() {
                    Some(Ok(node)) => node,
                    Some(Err(e)) => return Err(e),
                    None => {
                        return Err(ParseError::UnexpectedEOF(Token::Ident(
                            "PARAM_DEFAULT".to_string(),
                            LineInfo::default(),
                        )))
                    }
                };

                args.push((name, t, Some(default)))
            } else {
                args.push((name, t, None))
            }
        }

        self.expect_chars(&")", true)?;

        Ok(args)
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

    pub fn parse_block_expr(&mut self) -> Result<ParseBlock, ParseError> {
        self.expect_chars(&"{", true)?;

        let mut body: Vec<AstNode> = vec![];

        loop {
            match self.expect_chars(&"}", true) {
                Ok(_) => break,
                Err(ParseError::ExpectedToken(_, _)) => (),
                Err(e) => return Err(e),
            }

            match self.next_ast_node() {
                Some(Ok(node)) => body.push(node),
                Some(Err(e)) => return Err(e),
                None => {
                    return Err(ParseError::UnexpectedEOF(Token::Debug(
                        "STATEMENT".to_string(),
                    )))
                }
            }
        }

        Ok(ParseBlock::Plain(body.into_boxed_slice()))
    }

    pub fn parse_primary_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let token = match self.lexer.next_token()? {
            Ok(token) => token,
            Err(e) => return Some(Err(ParseError::LexError(e))),
        };

        let mut left = match token {
            Token::Byte(b, _) => {
                AstNode::ByteLiteral(b)
            }

            Token::Char(c, line_info) => {
                if c == '[' {
                    return match self.parse_array_expr()? {
                        Ok(node) => Some(Ok(node)),
                        Err(e) => Some(Err(e)),
                    };
                }

                let Some(next) = self.next_ast_node() else {
                    return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                        "EXPRESSION".to_string(),
                    ))));
                };

                let Ok(next) = next else {
                    return Some(Err(next.err().unwrap()));
                };

                if PREFIX_OPS.contains(&c.to_string().as_str()) {
                    return Some(Ok(AstNode::PrefixOp(c.to_string(), Indirection::new(next))))
                } else if c == '(' {
                    return match self.expect_char(&')', true) {
                        Err(e) => Some(Err(e)),
                        Ok(_) => self.parse_call_expr(next.clone()),
                    };
                } else {
                    return Some(Err(ParseError::InvalidToken(Token::Char(c, line_info))));
                }

                next
            }

            Token::String(s, _) => AstNode::StringLiteral(s),
            Token::Ident(i, _) => {
                if i == *"true" || i == *"false" {
                    AstNode::BooleanLiteral(i == "true")
                } else if i.to_lowercase() == "null" || i == "nil" {
                    AstNode::NullLiteral
                } else {
                    match self.parse_call_expr(AstNode::Identifier(i))? {
                        Ok(node) => node,
                        Err(e) => return Some(Err(e)),
                    }
                }
            },
            Token::Number(n, _) => AstNode::NumberLiteral(n),
            Token::Debug(_) => unreachable!("How on earth did a debug token get lexed???"),
        };

        if self.expect_chars(&"[", true).is_ok() {
            let Some(Ok(node)) = self.next_ast_node() else {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "INDEX".to_string(),
                ))));
            };

            left = AstNode::IdxAccess(Indirection::new(left.clone()), Indirection::new(node));

            match self.expect_chars(&"]", true) {
                Ok(_) => (),
                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_call_expr(&mut self, caller: AstNode) -> Option<Result<AstNode, ParseError>> {
        match caller {
            AstNode::Identifier(_) | AstNode::MemberExpr(_) => {
                if let Ok(_) = self.expect_chars(&"(", true) {
                    if let Some(Ok(Token::Char(c, _))) = self.lexer.peek_next_token() {
                        if c == ')' {
                            self.lexer.next_token();

                            return Some(Ok(AstNode::CallExpr {
                                callee: Rc::from(caller),
                                args: Box::from([]),
                            }));
                        }
                    }

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
            _ => Some(Ok(caller)),
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
                    None => {
                        return Err(ParseError::UnexpectedEOF(Token::Debug(
                            "PATH_SEG".to_string(),
                        )))
                    }
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
                    Some(Ok(Token::Number(begin, _))) => begin.to_string(),
                    Some(Ok(tk)) => {
                        return Err(ParseError::ExpectedToken(
                            Token::Ident("".to_string(), LineInfo::default()),
                            tk,
                        ))
                    }
                    Some(Err(e)) => return Err(ParseError::LexError(e)),
                    None => {
                        return Err(ParseError::UnexpectedEOF(Token::Debug(
                            "SEGMENT".to_string(),
                        )))
                    }
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
                Some(Ok(Token::Number(begin, _))) => begin.to_string(),
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
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
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
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
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
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
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
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"!=", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"||", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        } else if let Ok(op) = self.expect_chars(&"&&", true) {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))));
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
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "PATH".to_string(),
                ))))
            }
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
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))))
            }
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
        };

        Some(Ok(AstNode::DefStmt {
            name,
            def_type,
            value: Rc::from(value),
        }))
    }

    pub fn parse_include_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"include", true).unwrap();

        let path = match self.parse_path_expr(None) {
            Some(Ok(AstNode::Path(path))) => path,
            Some(Ok(_)) => unreachable!(),
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "PATH".to_string(),
                ))))
            }
        };

        Some(Ok(AstNode::IncludeStmt(path)))
    }

    pub fn parse_if_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"if", true).unwrap();

        let cond = match self.parse_comparative_expr() {
            Some(Ok(cond)) => cond,
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "EXPRESSION".to_string(),
                ))))
            }
        };

        let main_body = match self.parse_block_expr() {
            Ok(block) => block,
            Err(e) => return Some(Err(e)),
        };

        if self.expect_ident(&"else", true).is_ok() {
            let else_clause = match self.parse_block_expr() {
                Ok(block) => block,
                Err(e) => return Some(Err(e)),
            };

            return Some(Ok(AstNode::IfExpr {
                cond: Rc::from(cond),
                block: main_body,
                else_clause,
            }));
        }

        Some(Ok(AstNode::IfStmt {
            cond: Rc::from(cond),
            block: main_body,
        }))
    }

    pub fn parse_fn_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"fn", true).unwrap();

        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, ..))) => name,
            Some(Ok(tk)) => return Some(Err(ParseError::InvalidToken(tk))),
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "FN_NAME".to_string(),
                ))))
            }
        };

        let tg_args = if self.expect_chars(&"<", false).is_ok() {
            match self.parse_tg_list() {
                Ok(v) => v,
                Err(e) => return Some(Err(e)),
            }
        } else {
            Default::default()
        };

        let args = match self.parse_args_list() {
            Ok(args) => args.into_boxed_slice(),
            Err(e) => return Some(Err(e)),
        };

        let mut modifiers = vec![];

        while let Some(Ok(Token::Ident(m, _))) = self.lexer.peek_next_token() {
            let Ok(m) = Modifier::from_str(&*m) else {
                break
            };

            modifiers.push(m);

            self.lexer.next_token().unwrap().unwrap();
        }

        match self.expect_chars(&"->", true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };

        let ret_type = match self.parse_type() {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        let code = match self.parse_block_expr() {
            Ok(block) => block,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::FnExpr {
            name,
            ret_type,
            args,
            code,
            type_generics: tg_args,
            modifiers: modifiers.into_boxed_slice(),
        }))
    }

    pub fn parse_extern_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"extern", true).unwrap();
        
        let stmt = match self.lexer.peek_next_token() {
            Some(Ok(Token::Ident(s, _))) => s,
            Some(Ok(tk)) => return Some(Err(ParseError::InvalidToken(tk))),
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            None => return Some(Err(ParseError::UnexpectedEOF(Token::Debug("STMT".into()))))
        };

        match &*stmt {
            "def" => self.parse_extern_def_stmt(),
            "fn" => self.parse_extern_fn_stmt(),
            stmt => unimplemented!("extern {stmt}s.")
        }
    }

    pub fn parse_extern_fn_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"fn", true).unwrap();
        
        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, ..))) => name,
            Some(Ok(tk)) => return Some(Err(ParseError::InvalidToken(tk))),
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "FN_NAME".to_string(),
                ))))
            }
        };

        let args = match self.parse_args_list() {
            Ok(args) => args.into_boxed_slice(),
            Err(e) => return Some(Err(e)),
        };

        match self.expect_chars(&"->", true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };

        let ret_type = match self.parse_type() {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::ExternFn {
            name,
            ret_type,
            args,
        }))
    }

    pub fn parse_extern_def_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"def", true).unwrap();

        let def_type = match self.parse_type() {
            Ok(def_type) => def_type,
            Err(e) => return Some(Err(e)),
        };

        let name = match self.lexer.next_token() {
            None => {
                return Some(Err(ParseError::UnexpectedEOF(Token::Debug(
                    "PATH".to_string(),
                ))))
            }
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    Token::Ident("NAME".to_string(), LineInfo::default()),
                    tk,
                )))
            }
        };

        Some(Ok(AstNode::ExternDef {
            name,
            def_type
        }))
    }

    pub fn parse_return_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"return", true).unwrap();

        let value = match self.next_ast_node() {
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        Some(Ok(AstNode::ReturnStmt(Indirection::new(value))))
    }

    pub fn parse_for_in_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        self.expect_ident(&"for", true).unwrap();

        let var = match self.lexer.next_token() {
            Some(Ok(Token::Ident(v, _))) => v,
            Some(Ok(tk)) => return Some(Err(ParseError::InvalidToken(tk))),
            Some(Err(e)) => return Some(Err(ParseError::LexError(e))),
            None => return Some(Err(ParseError::UnexpectedEOF(Token::Debug("VAR".to_string())))),
        };

        self.expect_ident(&"in", true).unwrap();

        let of = match self.next_ast_node()? {
            Err(e) => return Some(Err(e)),
            Ok(n) => n
        };

        let block = match self.parse_block_expr() {
            Ok(b) => b,
            Err(e) => return Some(Err(e))
        };

        Some(Ok(AstNode::ForInExpr {
            var,
            of: Indirection::new(of),
            block,
        }))
    }

    pub fn next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        if let Some(Ok(Token::Ident(ident, _))) = self.lexer.peek_next_token() {
            match ident.as_str() {
                "def" => self.parse_def_stmt(),
                "include" => self.parse_include_stmt(),
                "if" => self.parse_if_expr(),
                "fn" => self.parse_fn_expr(),
                "extern" => self.parse_extern_stmt(),
                "return" => self.parse_return_stmt(),
                "for" => self.parse_for_in_expr(),
                _ => self.parse_comparative_expr(),
            }
        } else {
            self.parse_comparative_expr()
        }
    }

    pub fn parse_as_program(&mut self) -> OneOf<AstNode, Box<[ParseError]>> {
        let errors = self
            .flat_map(|node| if let Err(e) = node { [Some(e)] } else { [None] })
            .flatten()
            .collect::<Vec<ParseError>>();

        if !errors.is_empty() {
            return OneOf::Second(errors.into_boxed_slice());
        }

        let ok_nodes = self
            .filter_map(Result::ok)
            .collect::<Vec<AstNode>>();

        OneOf::First(AstNode::Program(ok_nodes.into_boxed_slice()))
    }

    pub fn peek_next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        let prev_state = self.state();

        let node = self.next_ast_node();

        self.reset_to_state(prev_state);

        node
    }
}
