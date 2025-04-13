#![allow(clippy::unwrap_used)]

use crate::errors::CompilationError;
use crate::lexer::StreamedLexer;
use crate::states::{ParserState, WithState};
use crate::tokens::{LineInfo, Token};
use crate::utils::Indirection;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;
use std::rc::Rc;
use std::str::FromStr;
use std::string::ToString;
use either::Either;

pub const MATCH_OPS: &[&str] = &[">", "<", "!="];

pub const BITWISE_OPS: &[&str] = &["==", "&&", "||", ">>", "<<", "&", "|", "="];
pub const ADDITIVE_OPS: &[&str] = &["+", "-"];
pub const MULTIPLICATIVE_OPS: &[&str] = &["*", "/", "%"];
pub const EXPONENTIAL_OPS: &[&str] = &["^"];
pub const PREFIX_OPS: &[&str] = &["!", "-", "+", "*", "&"];
pub const COMPARATIVE_OPS: &[&str] = &["!=", "==", "<", ">", "<=", ">=", "||", "&&", "!&&", "!||", "!&", "!|"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Modifier {
    /// Export the symbol this is used on
    Export,

    /// The returned value will be freed at the end of the caller's scope (at a return stmt)
    AutoFree,

    /// The developer must free the returned value manually.
    /// Functions marked with alloc should use this or auto_free.
    /// When the returned value is passed to a function with the dealloc modifier
    /// the compiler considers the value freed.
    MustFree,

    /// Indicates to the compiler that this function deallocates memory.
    /// These functions should have one pointer argument.
    Dealloc,

    /// Indicates to the compiler that this function allocates memory.
    /// This should be used with either must_free or auto_free.
    Alloc,

    /// Indicates to the compiler that this function should not be mangled.
    /// This is always used on main functions.
    NoMangle,
    
    /// Indicates to the compiler that whoever wrote this did not know what they were doing,
    /// meaning the compiler will output a warning when it is declared or defined.
    StupidThing,
}

impl FromStr for Modifier {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "export" | "public" | "pub" => Ok(Modifier::Export),
            "autofree" | "auto_free" => Ok(Modifier::AutoFree),
            "mustfree" | "must_free" => Ok(Modifier::MustFree),
            "alloc" | "allocates" => Ok(Modifier::Alloc),
            "dealloc" | "deallocates" => Ok(Modifier::Dealloc),
            "nomangle" | "no_mangle" => Ok(Modifier::NoMangle),
            "stupid_thing" | "stupidthing" | "donottrustthis" | "do_not_trust_this" | "probably_broken" | "probablybroken" => Ok(Modifier::StupidThing),
            m => Err(format!("Invalid modifier {m}")),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum ParseType {
    IdentType(String),

    PointerType {
        points_to: Indirection<ParseType>,
        is_mutable: bool,
        is_nullable: bool,
    },

    FatPointerType {
        points_to: Indirection<ParseType>,
        is_mutable: bool,
        is_nullable: bool,
    },

    Slice {
        points_to: Indirection<ParseType>,
        length: u32,
        is_mutable: bool,
        is_nullable: bool,
    },

    FuncPtr(Box<[ParseType]>, Rc<ParseType>),
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
            ParseType::PointerType {
                points_to,
                is_nullable,
                is_mutable,
            } => write!(f, "*{}{} {points_to}", if *is_mutable { "mut" } else { "const" }, if *is_nullable { "?" } else { "" }),
            ParseType::FatPointerType {
                points_to,
                is_nullable,
                is_mutable,
            } => write!(f, "*{}{} [{points_to}]", if *is_mutable { "mut" } else { "const" }, if *is_nullable { "?" } else { "" }),
            ParseType::Slice {
                points_to,
                is_nullable,
                is_mutable,
                length,
            } => write!(f, "*{}{} {length}[{points_to}]", if *is_mutable { "mut" } else { "const" }, if *is_nullable { "?" } else { "" }),
            ParseType::FuncPtr(args, ret) => write!(
                f,
                "fn({A}) -> {ret}",
                A = args
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
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
            TypeBound::Compound(bounds) => write!(
                f,
                "{B}",
                B = bounds
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<_>>()
                    .join(" + ")
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MacroArgKind {
    Any,
    Type,
    Expr,
    Literal,
    Path,
    Ident,
    Stmt,
}

impl MacroArgKind {
    fn from_str(file: &PathBuf, macro_name: &str, s: &str) -> Result<Self, ParseError> {
        match s {
            "all" | "any" => Ok(MacroArgKind::Any),
            "type" => Ok(MacroArgKind::Type),
            "expr" => Ok(MacroArgKind::Expr),
            "lit" => Ok(MacroArgKind::Literal),
            "path" => Ok(MacroArgKind::Path),
            "ident" => Ok(MacroArgKind::Ident),
            "stmt" => Ok(MacroArgKind::Stmt),
            s => Err(ParseError::UnknownNodeType(file.clone(), macro_name.to_owned(), s.to_owned()))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    arguments: HashMap<String, MacroArgKind>,
}

impl Display for MacroArgKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroArgKind::Any => write!(f, "any/all"),
            MacroArgKind::Type => write!(f, "type"),
            MacroArgKind::Expr => write!(f, "expr"),
            MacroArgKind::Literal => write!(f, "lit"),
            MacroArgKind::Path => write!(f, "path"),
            MacroArgKind::Ident => write!(f, "ident"),
            MacroArgKind::Stmt => write!(f, "stmt"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub operator: String,
    pub right: Indirection<AstNode>,
    pub is_else: bool,
    pub code: ParseBlock,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    // --- EXPRESSIONS --- //
    NumberLiteral(LineInfo, f64),
    ByteLiteral(LineInfo, u8),
    StringLiteral(LineInfo, String),
    ArrayLiteral(LineInfo, Box<[AstNode]>),
    BooleanLiteral(LineInfo, bool),
    NullLiteral(LineInfo),
    Identifier(LineInfo, String),
    InfixOp(LineInfo,  Rc<AstNode>, String, Rc<AstNode>),
    PrefixOp(LineInfo,  String, Indirection<AstNode>),
    PostfixOp(LineInfo,  Rc<AstNode>, String),
    Path(LineInfo,  Box<[String]>),
    MemberExpr(LineInfo,  Box<[String]>),
    IdxAccess(
        LineInfo,
        Indirection<AstNode>,
        Indirection<AstNode>,
    ),
    CallExpr {
        line_info: LineInfo,
        callee: Rc<AstNode>,
        args: Box<[AstNode]>,
    },
    AsExpr(LineInfo,  Rc<AstNode>, ParseType),
    AbortingAsExpr(LineInfo,  Rc<AstNode>, ParseType),
    IfExpr {
        line_info: LineInfo,
        cond: Rc<AstNode>,
        block: ParseBlock,
        else_clause: ParseBlock,
    },
    
    MatchExpr {
        line_info: LineInfo,
        matchee: Rc<AstNode>,
        arms: Box<[MatchArm]>,
    },

    DataInitExpr {
        name: String,
        fields: Vec<(String, Indirection<AstNode>)>,
        line_info: LineInfo,
    },
    
    // --- Statements and expressions at the same time? --- //
    
    GuardClause {
        line_info: LineInfo,
        cond: Indirection<AstNode>,
        else_code: ParseBlock,
    },

    // --- Statements --- //
    
    ForInStmt {
        line_info: LineInfo,
        var: String,
        of: Indirection<AstNode>,
        block: ParseBlock,
    },
    
    ForCondStmt {
        line_info: LineInfo,
        var: String,
        threshold: u32,
        operator: Indirection<AstNode>,
        block: ParseBlock,
    },
    
    FnStmt {
        line_info: LineInfo,
        of: Option<String>,
        name: String,
        ret_type: ParseType,
        args: Box<[(String, ParseType, Option<AstNode>)]>,
        type_generics: HashMap<String, Option<TypeBound>>,
        code: ParseBlock,
        modifiers: Box<[Modifier]>,
    },
    
    LetStmt {
        name_info: LineInfo,
        name: String,
        def_type: Option<ParseType>,
        value: Rc<AstNode>,
    },

    MutStmt {
        name_info: LineInfo,
        name: String,
        def_type: Option<ParseType>,
        value: Rc<AstNode>,
    },

    DataStmt {
        name: String,
        fields: Vec<(bool, String, ParseType)>, // Vec<(is_mutable, name, type)>
        modifiers: Vec<Modifier>,
        line_info: LineInfo,
    },

    WhileStmt {
        line_info: LineInfo,
        cond: Rc<AstNode>,
        code: ParseBlock,
    },

    /// self.0 is always an AstNode::Path
    IncludeStmt(LineInfo,  Box<[String]>),

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
        args: Box<[(String, ParseType, Option<AstNode>)]>,
    },

    DeferStmt(LineInfo, ParseBlock),
    ReturnStmt(LineInfo, Indirection<AstNode>),

    TypeAlias(LineInfo, String, ParseType),

    // --- special --- //
    SizeOf(LineInfo, ParseType), // @sizeof builtin macro
    MacroUseArg(LineInfo, String), // $X
}

impl Display for AstNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::NumberLiteral(n, ..) => write!(f, "{n}"),
            AstNode::StringLiteral(s, ..) => write!(f, "\"{s}\""),
            AstNode::ArrayLiteral(arr, ..) => write!(f, "{arr:?}"),
            AstNode::BooleanLiteral(b, ..) => write!(f, "{b}"),
            AstNode::NullLiteral(..) => write!(f, "null"),
            AstNode::Identifier(i, ..) => write!(f, "{i}"),
            AstNode::InfixOp(l, o, r, ..) => write!(f, "{l} {o} {r}"),
            AstNode::PrefixOp(o, v, ..) => write!(f, "{o}({v})"),
            AstNode::PostfixOp(v, o, ..) => write!(f, "({v}){o}"),
            AstNode::Path(_, p, ..) => write!(f, "{}", p.join("::")),
            AstNode::MemberExpr(_, p, ..) => write!(f, "{}", p.join(".")),
            AstNode::IdxAccess(v, i, ..) => write!(f, "{v}[{i}]"),
            AstNode::DataInitExpr { name, .. } => write!(f, "{name} {{ ... }}"),
            AstNode::CallExpr { args, callee, .. } => write!(
                f,
                "({callee})({})",
                args.iter()
                    .map(|n| format!("{n}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            AstNode::AsExpr(v, t, ..) => write!(f, "({v}) as {t}"),
            AstNode::AbortingAsExpr(v, t, ..) => write!(f, "({v}) as! {t}"),
            AstNode::GuardClause { cond, .. } => write!(f, "guard {cond} else {{ ... }}"),
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
                ..
            } => write!(f, "if ({cond}) {{\n{block}}} else {{\n{else_clause}}}"),
            AstNode::MatchExpr {
                matchee,
                ..
            } => write!(f, "match ({matchee}) {{...}}"),
            AstNode::FnStmt {
                name,
                ret_type,
                args,
                ..
            } => write!(f, "fn {name}({args:?}) -> {ret_type} {{ ... }}"),
            AstNode::LetStmt {
                name,
                def_type,
                value,
                ..
            } => write!(f, "let {name}: {def_type:?} = {value}"),
            AstNode::MutStmt {
                name,
                def_type,
                value,
                ..
            } => write!(f, "mut {name}: {def_type:?} = {value}"),
            AstNode::IncludeStmt(_, p, ..) => write!(f, "include {P}", P = p.join("::")),
            AstNode::IfStmt { cond, block, .. } => write!(f, "if ({cond}) {{\n{block}\n}}"),
            AstNode::DataStmt { name, .. } => write!(f, "data {name} {{ ... }}"),
            AstNode::ExternFn {
                name,
                ret_type,
                args,
                ..
            } => write!(f, "extern fn {name}({args:?}) -> {ret_type}"),
            AstNode::TypeAlias(_, name, t, ..) => write!(f, "type {name} = {t}"),
            AstNode::WhileStmt { cond, .. } => write!(f, "while {cond} {{ ... }}"),
            AstNode::ReturnStmt(_, v, ..) => write!(f, "return {v}"),
            AstNode::ForInStmt { var, of, block, .. } => write!(f, "for {var} in {of} {{\n{block}\n}}"),
            AstNode::ForCondStmt { var, operator, threshold, block, .. } => write!(f, "for {var} {operator} {threshold} {{\n{block}\n}}"),
            AstNode::DeferStmt(_, block, ..) => write!(f, "defer {{\n{block}\n}}"),
            AstNode::ByteLiteral(_, b, ..) => write!(f, "'{C}'", C = *b as char),
            AstNode::SizeOf(_, t, ..) => write!(f, "@sizeof({t})"),
            AstNode::MacroUseArg(_, name, ..) => write!(f, "${name}"),
        }
    }
}

impl AstNode {
    fn line_info(&self) -> LineInfo {
        *match self {
            AstNode::NumberLiteral(l, ..) => l,
            AstNode::ByteLiteral(l, ..) => l,
            AstNode::StringLiteral(l, ..) => l,
            AstNode::ArrayLiteral(l, ..) => l,
            AstNode::BooleanLiteral(l, ..) => l,
            AstNode::NullLiteral(l) => l,
            AstNode::Identifier(l, ..) => l,
            AstNode::InfixOp(l, ..) => l,
            AstNode::PrefixOp(l, ..) => l,
            AstNode::PostfixOp(l, ..) => l,
            AstNode::GuardClause { line_info, .. } => line_info,
            AstNode::DataInitExpr { line_info, .. } => line_info,
            AstNode::Path(l, ..) => l,
            AstNode::MemberExpr(l, _) => l,
            AstNode::IdxAccess(l, ..) => l,
            AstNode::CallExpr { line_info, .. } => line_info,
            AstNode::AsExpr(l, ..) => l,
            AstNode::AbortingAsExpr(l, ..) => l,
            AstNode::IfExpr { line_info, .. } => line_info,
            AstNode::MatchExpr { line_info, .. } => line_info,
            AstNode::ForInStmt { line_info, .. } => line_info,
            AstNode::ForCondStmt { line_info, .. } => line_info,
            AstNode::FnStmt { line_info, .. } => line_info,
            AstNode::LetStmt { name_info, .. } => name_info,
            AstNode::MutStmt { name_info, .. } => name_info,
            AstNode::WhileStmt { line_info, .. } => line_info,
            AstNode::IncludeStmt(l, ..) => l,
            AstNode::IfStmt  { line_info, .. } => line_info,
            AstNode::ExternFn  { line_info, .. } => line_info,
            AstNode::DeferStmt(l, ..) => l,
            AstNode::DataStmt { line_info, .. } => line_info,
            AstNode::ReturnStmt(l, ..) => l,
            AstNode::TypeAlias(l, ..) => l,
            AstNode::SizeOf(l, ..) => l,
            AstNode::MacroUseArg(l, ..) => l,
        }
    }
    
    fn is_stmt(&self) -> bool {
        matches!(self, Self::ForInStmt { .. }  |
            Self::FnStmt { .. }     |
            Self::LetStmt { .. }    |
            Self::MutStmt { .. }    |
            Self::WhileStmt { .. }  |
            Self::IncludeStmt(..)   |
            Self::IfStmt { .. }     |
            Self::ExternFn { .. }   |
            Self::ReturnStmt(..)    |
            Self::TypeAlias(..))
    }

    fn is_special(&self) -> bool {
        matches!(self, Self::MacroUseArg(..) | Self::SizeOf(..))
    }
    
    fn is_expr(&self) -> bool {
        !self.is_stmt() && !self.is_special()
    }
    
    fn is_literal(&self) -> bool {
        matches!(self, Self::BooleanLiteral(..) |
            Self::ArrayLiteral(..)   |
            Self::NullLiteral(..)    |
            Self::NumberLiteral(..)  |
            Self::ByteLiteral(..)    |
            Self::StringLiteral(..))
    }
}

type ParseError = CompilationError;

#[derive(Debug, PartialEq)]
pub struct StreamedParser {
    pub(crate) lexer: StreamedLexer,
    file: PathBuf,
    macros: HashMap<String, Macro>
}

impl WithState for StreamedParser {
    type ToState = ParserState;

    fn from_state(state: Self::ToState) -> Self {
        let lexer = StreamedLexer::from_state(state.lexer_state);
        let file = lexer.reader.reader.path().to_path_buf();
        let macros = state.macros;

        Self {
            lexer,
            file,
            macros
        }
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        self.lexer = StreamedLexer::from_state(state.lexer_state)
    }

    fn state(&self) -> Self::ToState {
        ParserState::new(self.lexer.state(), self.macros.clone())
    }
}

impl Clone for StreamedParser {
    fn clone(&self) -> StreamedParser {
        StreamedParser {
            lexer: self.lexer.clone(),
            file: self.lexer.reader.reader.path().to_path_buf(),
            macros: self.macros.clone()
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
        let file = lexer.reader.reader.path().to_path_buf();

        Self { lexer, file, macros: [
            ("sizeof".into(), Macro {
                arguments: [("ty".into(), MacroArgKind::Type)].into(),
            })
        ].into() }
    }

    pub fn expect_ident(
        &mut self,
        chars: &str,
        mutate: bool,
    ) -> Result<LineInfo, ParseError> {
        let tk = self.lexer.peek_next_token();

        match tk {
            None => Err(ParseError::UnexpectedEOF(
                self.file.clone(),
                chars.to_string(),
            )),
            Some(Err(e)) => Err(e),
            Some(Ok(Token::Ident(ref c, l))) => {
                if c.as_str() == chars {
                    if mutate {
                        self.lexer.next_token();
                    }

                    Ok(l)
                } else {
                    Err(ParseError::ExpectedToken(
                        self.file.clone(),
                        Token::Ident(chars.to_string(), LineInfo::default()),
                        match tk {
                            Some(v) => v,
                            None => Err(ParseError::UnexpectedEOF(
                                self.file.clone(),
                                "IDENTIFIER".into(),
                            )),
                        }?,
                    ))
                }
            }
            _ => Err(ParseError::ExpectedToken(
                self.file.clone(),
                Token::Ident(chars.to_string(), LineInfo::default()),
                match tk {
                    Some(v) => v,
                    None => Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "IDENTIFIER".into(),
                    )),
                }?,
            )),
        }
    }

    pub fn expect_chars(
        &mut self,
        chars: &str,
        mutate: bool,
        start_pos: &LineInfo,
    ) -> Result<LineInfo, ParseError> {
        for char in chars.to_string()[0..chars.len() - 1].chars() {
            self.expect_char(&char, mutate)?;
        }

        let end_pos = self.expect_char(&chars.chars().last().unwrap(), mutate)?;

        Ok(LineInfo::new(
            start_pos.begin_char(),
            start_pos.end_char(),
            end_pos.begin_line(),
            end_pos.end_line(),
        ))
    }

    pub fn expect_char(&mut self, c: &char, m: bool) -> Result<LineInfo, ParseError> {
        let tk = self.lexer.peek_next_token();

        let Some(tk) = tk else {
            return Err(ParseError::UnexpectedEOF(
                self.file.clone(),
                c.to_string(),
            ));
        };

        let Ok(tk) = tk else {
            return Err(ParseError::UnexpectedEOF(
                self.file.clone(),
                c.to_string(),
            ));
        };

        if let Token::Char(char, l) = tk {
            if char == *c {
                if m {
                    self.lexer.next_token();
                }

                Ok(l)
            } else {
                Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Char(char, tk.line_info()),
                    Token::Char(c.to_owned(), tk.line_info()),
                ))
            }
        } else {
            Err(ParseError::ExpectedToken(
                self.file.clone(),
                Token::Char(c.to_owned(), tk.line_info()),
                tk,
            ))
        }
    }

    fn parse_fn_type(&mut self) -> Result<ParseType, ParseError> {
        self.expect_chars(&"(", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        let mut is_first = true;

        if self.expect_chars(&")", false, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            is_first = false
        }

        let mut args: Vec<_> = vec![];

        while self.expect_chars(&",", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() || is_first {
            is_first = false;

            args.push(self.parse_type()?)
        }

        self.expect_chars(&")", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        self.expect_chars(&"->", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        let ret_type = self.parse_type()?;

        Ok(ParseType::FuncPtr(
            args.into_boxed_slice(),
            Rc::new(ret_type),
        ))
    }

    fn parse_ident_type(&mut self) -> Result<ParseType, ParseError> {
        let t = match self.lexer.peek_next_token() {
            Some(Ok(Token::Ident(t, _))) => t,
            Some(Ok(tk)) => {
                return Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Debug("TYPE_NAME".into()),
                    tk,
                ))
            }
            Some(Err(e)) => return Err(e),
            None => {
                return Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "TYPE".to_string(),
                ))
            }
        };

        self.lexer.next_token();

        if &*t == "fn" {
            return self.parse_fn_type();
        }

        Ok(ParseType::IdentType(t))
    }

    fn parse_type(&mut self) -> Result<ParseType, ParseError> {
        if self.expect_chars(&"*", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let is_mutable = self.expect_ident(&"mut", true).is_ok();

            if !is_mutable {
                self.expect_ident(&"const", true)?;
            }

            let is_nullable = self.expect_chars(&"?", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok();

            if self.expect_char(&'[', true).is_ok() {
                let left = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Err(e),
                };

                self.expect_chars(&"]", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

                return Ok(ParseType::FatPointerType {
                    points_to: Indirection::new(left),
                    is_nullable,
                    is_mutable
                });
            }

            // parse slice
            if let Some(Ok(Token::Number(l, _))) = self.lexer.peek_next_token() {
                self.lexer.next_token();

                self.expect_chars(&"[", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

                let left = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Err(e),
                };

                self.expect_chars(&"]", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

                return Ok(ParseType::Slice {
                    points_to: Indirection::new(left),
                    length: l as u32,
                    is_nullable,
                    is_mutable,
                });
            }

            let left = match self.parse_type() {
                Ok(t) => t,
                Err(e) => return Err(e),
            };

            return Ok(ParseType::PointerType {
                points_to: Indirection::new(left),
                is_mutable,
                is_nullable,
            });
        }

        let left = match self.parse_ident_type() {
            Ok(t) => t,
            Err(e) => return Err(e),
        };

        Ok(left)
    }

    pub fn parse_macro_list(&mut self, left: Option<AstNode>) -> Result<Vec<Either<AstNode, ParseType>>, ParseError> {
        let begin = (|| {
            let Some(left) = left else {
                let next = self.next_ast_node();

                let next = match next {
                    Some(Ok(node)) => Either::Left(node),
                    Some(Err(e)) => match self.parse_type() {
                        Ok(ty) => Either::Right(ty),
                        Err(e) => return Err(e)
                    },
                    _ => todo!("Error here"),
                };

                return Ok(next);
            };

            Ok(Either::Left(left))
        })()?;

        let mut items: Vec<Either<AstNode, ParseType>> = vec![begin];

        while self.expect_chars(&",", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let next = self.next_ast_node();

            let next = match next {
                Some(Ok(node)) => Either::Left(node),
                Some(Err(e)) => match self.parse_type() {
                    Ok(ty) => Either::Right(ty),
                    Err(e) => return Err(e)
                },
                _ => break,
            };

            items.push(next)
        }

        Ok(items)
    }

    pub fn parse_list(&mut self, left: Option<AstNode>) -> Result<Vec<AstNode>, ParseError> {
        let begin = match (|| {
            let Some(left) = left else {
                let tk = self.next_ast_node();

                return Ok(match tk {
                    Some(Ok(node)) => node,
                    Some(Err(e)) => return Err(e),
                    None => {
                        return Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "EXPR".to_string(),
                        ))
                    }
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(ParseError::UnexpectedEOF(..)) => return Ok(vec![]),
            Err(e) => return Err(e),
        };

        let mut items: Vec<AstNode> = vec![begin];

        while self.expect_chars(&",", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
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
            None => {
                return Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "TYPE BOUND".into(),
                ))
            }
            Some(Err(e)) => return Err(e),
            Some(Ok(Token::Ident(i, _))) if i == "iter".to_string() => {
                self.expect_chars(&"[", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

                let iterate_over = self.parse_type()?;

                self.expect_chars(&"]", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

                TypeBound::Iterator(Indirection::new(iterate_over))
            }
            Some(Ok(Token::Char(c, _))) if c == '!' => {
                TypeBound::Not(Indirection::new(self.parse_tg_bound()?))
            }
            Some(Ok(t)) => return Err(ParseError::InvalidToken(self.file.clone(), t)),
        };

        while self.expect_chars(&"+", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let right = self.parse_tg_bound()?;

            match right {
                TypeBound::Compound(b) => {
                    left = TypeBound::Compound([&[left], b.as_ref()].concat().into_boxed_slice())
                }
                b => left = b,
            }
        }

        Ok(left)
    }

    pub fn parse_tg_list(&mut self) -> Result<HashMap<String, Option<TypeBound>>, ParseError> {
        self.expect_chars(&"<", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        if self.expect_chars(&">", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            return Ok(Default::default());
        }

        let mut args: HashMap<String, Option<TypeBound>> = Default::default();
        let mut is_first = true;

        while self.expect_chars(&",", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() || is_first {
            is_first = false;

            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => {
                    return Err(ParseError::ExpectedToken(
                        self.file.clone(),
                        Token::Ident("TG_NAME".to_string(), LineInfo::default()),
                        tk,
                    ))
                }
                Some(Err(e)) => return Err(e),
                None => {
                    return Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "PARAMETER NAME".to_string(),
                    ))
                }
            };

            if self.expect_chars(&":", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                args.insert(name, Some(self.parse_tg_bound()?));
            } else {
                args.insert(name, None);
            }
        }

        self.expect_chars(&">", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        Ok(args)
    }

    pub fn parse_args_list(
        &mut self,
        allow_parenthesis_exclusion: bool,
    ) -> Result<Vec<(String, ParseType, Option<AstNode>)>, ParseError> {
        if let Err(e) = self.expect_chars(&"(", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
            if !allow_parenthesis_exclusion {
                return Err(e)
            }
            
            return Ok(Default::default());
        };

        if self.expect_chars(&")", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            return Ok(vec![]);
        }

        let mut args: Vec<(String, ParseType, Option<AstNode>)> = vec![];
        let mut is_first = true;

        while self.expect_chars(&",", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() || is_first {
            is_first = false;

            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => {
                    return Err(ParseError::ExpectedToken(
                        self.file.clone(),
                        Token::Ident("PARAM_NAME".to_string(), LineInfo::default()),
                        tk,
                    ))
                }
                Some(Err(e)) => return Err(e),
                None => {
                    return Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "PARAMETER NAME".to_string(),
                    ))
                }
            };
            
            self.expect_chars(&":", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

            let t = self.parse_type()?;

            if self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                let default = match self.next_ast_node() {
                    Some(Ok(node)) => node,
                    Some(Err(e)) => return Err(e),
                    None => {
                        return Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "PARAMETER DEFAULT".to_string(),
                        ))
                    }
                };

                args.push((name, t, Some(default)))
            } else {
                args.push((name, t, None))
            }
        }

        self.expect_chars(&")", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        Ok(args)
    }

    pub fn parse_array_expr(&mut self, begin: &LineInfo) -> Option<Result<AstNode, ParseError>> {
        let args = match self.parse_list(None) {
            Ok(args) => args,
            Err(e) => return Some(Err(e)),
        };

        match self.expect_chars(&"]", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
            Ok(_) => Some(Ok(AstNode::ArrayLiteral(*begin, args.into_boxed_slice()))),
            Err(e) => Some(Err(e)),
        }
    }

    pub fn parse_block_expr(&mut self) -> Result<ParseBlock, ParseError> {
        self.expect_chars(&"{", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line))?;

        let mut body: Vec<AstNode> = vec![];

        loop {
            match self.expect_chars(&"}", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
                Ok(_) => break,
                Err(ParseError::ExpectedToken(..)) => (),
                Err(e) => return Err(e),
            }

            match self.next_ast_node() {
                Some(Ok(node)) => body.push(node),
                Some(Err(e)) => return Err(e),
                None => {
                    return Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "STATEMENT".to_string(),
                    ))
                }
            }
        }

        Ok(ParseBlock::Plain(body.into_boxed_slice()))
    }

    pub fn parse_data_init_expr(&mut self, name: String, start: LineInfo) -> Option<Result<AstNode, ParseError>> {
        match self.expect_char(&'{', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        }
        
        let mut fields: Vec<(String, Indirection<AstNode>)> = vec![];

        while self.expect_char(&'.', true).is_ok() {
            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => {
                    return Some(Err(ParseError::ExpectedToken(
                        self.file.clone(),
                        Token::Ident("".into(), LineInfo::default()),
                        tk,
                    )))
                }
                Some(Err(e)) => return Some(Err(e)),
                None => {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "DATA INIT FIELD NAME".to_string()
                    )))
                }
            };
            
            match self.expect_char(&'=', true) {
                Ok(_) => (),
                Err(e) => return Some(Err(e)),
            }
            
            let value = match self.next_ast_node() {
                None => {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "DEF VALUE (EXPR)".to_string()
                    )))
                }
                Some(Ok(node)) => node,
                Some(Err(e)) => return Some(Err(e)),
            };
            
            println!(".{name} = {value:?}");

            let _ = self.expect_char(&',', true);

            fields.push((name, Indirection::new(value)))
        }

        match self.expect_char(&'}', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        }
        
        Some(Ok(AstNode::DataInitExpr {
            name,
            fields,
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line
            ),
        }))
    }

    pub fn parse_primary_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let token = match self.lexer.next_token()? {
            Ok(token) => token,
            Err(e) => return Some(Err(e)),
        };

        let mut left = match token {
            Token::Byte(b, l) => AstNode::ByteLiteral(l, b),

            Token::Char(c, line_info) => {
                if c == '@' {
                    let name = match self.lexer.next_token() {
                        Some(Ok(Token::Ident(name, _))) => name,
                        Some(Ok(tk)) => {
                            return Some(Err(ParseError::ExpectedToken(
                                self.file.clone(),
                                Token::Debug("MACRO_NAME".into()),
                                tk,
                            )))
                        }
                        Some(Err(e)) => return Some(Err(e)),
                        None => {
                            return Some(Err(ParseError::UnexpectedEOF(
                                self.file.clone(),
                                "MACRO NAME".to_string(),
                            )))
                        }
                    };

                    let _ = self.expect_char(&'(', true);

                    let args = match self.parse_macro_list(None) {
                        Ok(args) => args,
                        Err(e) => return Some(Err(e)),
                    };

                    let _ = self.expect_char(&')', true);

                    let Some(mac) = self.macros.get(&name) else {
                        return Some(Err(ParseError::UndefinedMacro(self.file.clone(), name)))
                    };

                    for (i, (arg, kind)) in mac.arguments.iter().enumerate() {
                        let error = ParseError::InvalidMacroArg {
                            file: self.file.clone(),
                            arg_idx: i,
                            arg_name: arg.clone(),
                            expected: kind.clone(),
                            macro_name: name.clone(),
                            got_node: args[i].clone(),
                        };

                        match kind {
                            MacroArgKind::Any => continue,
                            MacroArgKind::Type if args[i].is_left() => return Some(Err(error)),
                            MacroArgKind::Type => continue,
                            MacroArgKind::Expr => return if let Either::Left(ref n) = args[i] {
                                if n.is_expr() {
                                    continue
                                }

                                Some(Err(error))
                            } else {
                                Some(Err(error))
                            },
                            MacroArgKind::Literal => return if let Either::Left(ref n) = args[i] {
                                if n.is_literal() {
                                    continue
                                }

                                Some(Err(error))
                            } else {
                                Some(Err(error))
                            },
                            MacroArgKind::Path => return if let Either::Left(ref n) = args[i] {
                                if matches!(n, AstNode::Path(..)) {
                                    continue
                                }

                                Some(Err(error))
                            } else {
                                Some(Err(error))
                            },
                            MacroArgKind::Ident => return if let Either::Left(ref n) = args[i] {
                                if matches!(n, AstNode::Identifier(..)) {
                                    continue
                                }

                                Some(Err(error))
                            } else {
                                Some(Err(error))
                            },
                            MacroArgKind::Stmt => return if let Either::Left(ref n) = args[i] {
                                if n.is_stmt() {
                                    continue
                                }

                                Some(Err(error))
                            } else {
                                Some(Err(error))
                            },
                        }
                    }

                    match &*name {
                        _ => todo!("Implement custom macros")
                    }
                }

                if c == '[' {
                    return match self.parse_array_expr(&line_info)? {
                        Ok(node) => Some(Ok(node)),
                        Err(e) => Some(Err(e)),
                    };
                }

                let Some(next) = self.next_ast_node() else {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "EXPRESSION".to_string(),
                    )));
                };

                let next = match next {
                    Ok(n) => n,
                    Err(e) => return Some(Err(e)),
                };

                if PREFIX_OPS.contains(&c.to_string().as_str()) {
                    let info = LineInfo::new(
                        line_info.begin_char(),
                        next.line_info().end_char(),
                        line_info.begin_line(),
                        next.line_info().end_line(),
                    );
                    
                    AstNode::PrefixOp(info, c.to_string(), Indirection::new(next))
                } else if c == '(' {
                    match self.expect_char(&')', true) {
                        Err(e) => return Some(Err(e)),
                        Ok(_) => next.clone(),
                    }
                } else {
                    return Some(Err(ParseError::InvalidToken(
                        self.file.clone(),
                        Token::Char(c, line_info),
                    )))
                }
            }

            Token::String(s, l) => AstNode::StringLiteral(l, s),
            Token::Ident(i, l) => {
                if i == *"true" || i == *"false" {
                    AstNode::BooleanLiteral(l, i == "true")
                } else if i.to_lowercase() == "null" || i == "nil" {
                    AstNode::NullLiteral(l)
                } else {
                    if self.expect_char(&'{', false).is_ok() {
                        println!("DAT_INIT_EXPR");

                        match self.parse_data_init_expr(i, l) {
                            Some(Ok(node)) => node,
                            Some(Err(e)) => return Some(Err(e)),
                            None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "DATA INIT EXPR".to_string())))
                        }
                    } else {
                        match self.parse_call_expr(AstNode::Identifier(l, i))? {
                            Ok(node) => node,
                            Err(e) => return Some(Err(e)),
                        }
                    }
                }
            }
            Token::Number(n, l) => AstNode::NumberLiteral(l, n),
            Token::Debug(_) => unreachable!("How on earth did a debug token get lexed???"),
        };

        if self.expect_chars(&"[", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let Some(Ok(node)) = self.next_ast_node() else {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "INDEX".to_string(),
                )));
            };

            left = AstNode::IdxAccess(LineInfo::new(
                left.line_info().begin_char(),
                node.line_info().end_char(),
                left.line_info().begin_line(),
                node.line_info().end_line(),
            ), Indirection::new(left.clone()), Indirection::new(node));

            match self.expect_chars(&"]", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
                Ok(_) => (),
                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_call_expr(&mut self, caller: AstNode) -> Option<Result<AstNode, ParseError>> {
        match caller {
            AstNode::Identifier(..) | AstNode::MemberExpr(..) | AstNode::Path(..) => {
                if let Ok(_) = self.expect_chars(&"(", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
                    if self.expect_chars(&")", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                        return Some(Ok(AstNode::CallExpr {
                            line_info: LineInfo::new(
                                caller.line_info().begin_char(),
                                self.lexer.state().current_char,
                                caller.line_info().begin_line(),
                                self.lexer.state().current_line,
                            ),
                            callee: Rc::from(caller),
                            args: Box::from([]),
                        }));
                    }

                    let args = match self.parse_list(None) {
                        Ok(args) => args,
                        Err(e) => return Some(Err(e)),
                    };

                    match self.expect_chars(&")", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
                        Ok(_) => Some(Ok(AstNode::CallExpr {
                            line_info: LineInfo::new(
                                caller.line_info().begin_char(),
                                self.lexer.state().current_char,
                                caller.line_info().begin_line(),
                                self.lexer.state().current_line,  
                            ),
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
            let Some(AstNode::Identifier(_, left, ..)) = left else {
                let tk = self.lexer.next_token();

                return Ok(match tk {
                    Some(Ok(Token::Ident(begin, _))) => begin,
                    Some(Ok(tk)) => {
                        return Err(ParseError::ExpectedToken(
                            self.file.clone(),
                            Token::Ident("".to_string(), LineInfo::default()),
                            tk,
                        ))
                    }
                    Some(Err(e)) => return Err(e),
                    None => {
                        return Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "PATH SEGMENT".to_string(),
                        ))
                    }
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(e) => return Some(Err(e)),
        };

        let mut path: Vec<String> = vec![begin];

        while self.expect_chars(&"::", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let next = self.lexer.next_token();

            let next = match next {
                Some(Ok(Token::Ident(begin, _))) => begin,
                Some(Err(e)) => return Some(Err(e)),
                _ => break,
            };

            path.push(next)
        }

        // TODO: fix this
        self.parse_call_expr(AstNode::Path(LineInfo::default(), path.into_boxed_slice()))
    }

    pub fn parse_member_expr(
        &mut self,
        left: Option<AstNode>,
    ) -> Option<Result<AstNode, ParseError>> {
        let begin = match (|| {
            let Some(AstNode::Identifier(_, left, ..)) = left else {
                let tk = self.lexer.next_token();

                return Ok(match tk {
                    Some(Ok(Token::Ident(begin, _))) => begin,
                    Some(Ok(Token::Number(begin, _))) => begin.to_string(),
                    Some(Ok(tk)) => {
                        return Err(ParseError::ExpectedToken(
                            self.file.clone(),
                            Token::Ident("".to_string(), LineInfo::default()),
                            tk,
                        ))
                    }
                    Some(Err(e)) => return Err(e),
                    None => {
                        return Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "MEMBER SEGMENT".to_string(),
                        ))
                    }
                });
            };

            Ok(left)
        })() {
            Ok(p) => p,
            Err(e) => return Some(Err(e)),
        };

        let mut path: Vec<String> = vec![begin];

        while self.expect_chars(".", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let next = self.lexer.next_token();

            let next = match next {
                Some(Ok(Token::Ident(begin, _))) => begin,
                Some(Ok(Token::Number(begin, _))) => begin.to_string(),
                Some(Err(e)) => return Some(Err(e)),
                _ => break,
            };

            path.push(next)
        }

        // TODO: fix this
        self.parse_call_expr(AstNode::MemberExpr(LineInfo::default(), path.into_boxed_slice()))
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
            Err(e) => return Some(Err(e)),
            _ => (),
        };

        if let Ok(_) = self.expect_ident(&"as", true) {
            if self.expect_char(&'!', true).is_ok() {
                let right = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Some(Err(e)),
                };

                left = AstNode::AbortingAsExpr(LineInfo::new(
                    left.line_info().begin_char(),
                    self.lexer.state().current_char,
                    left.line_info().begin_line(),
                    self.lexer.state().current_line,
                ), Rc::from(left), right)
            }

            let right = match self.parse_type() {
                Ok(t) => t,
                Err(e) => return Some(Err(e)),
            };

            left = AstNode::AsExpr(LineInfo::new(
                left.line_info().begin_char(),
                self.lexer.state().current_char,
                left.line_info().begin_line(),
                self.lexer.state().current_line,
            ), Rc::from(left), right)
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
            Err(e) => return Some(Err(e)),
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if op == '.' {
            return self.parse_member_expr(Some(left));
        } else if op == ':' {
            return self.parse_path_expr(Some(left));
        } else if EXPONENTIAL_OPS.contains(&op.to_string().as_str()) {
            let _ = self.lexer.next_token();

            let Some(right) = self.parse_exponential_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXPRESSION".to_string()
                )));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(LineInfo::new(
                        left.line_info().begin_char(),
                        self.lexer.state().current_char,
                        left.line_info().begin_line(),
                        self.lexer.state().current_line,
                    ), Rc::from(left), op.to_string(), Rc::from(right))
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
            Err(e) => return Some(Err(e)),
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if MULTIPLICATIVE_OPS.contains(&op.to_string().as_str()) {
            let _ = self.lexer.next_token();

            let Some(right) = self.parse_multiplicative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXPRESSION".to_string()
                )));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(LineInfo::new(
                        left.line_info().begin_char(),
                        self.lexer.state().current_char,
                        left.line_info().begin_line(),
                        self.lexer.state().current_line,
                    ), Rc::from(left), op.to_string(), Rc::from(right))
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

        let tk = match tk {
            Ok(tk) => tk,
            Err(e) => return Some(Err(e)),
        };

        let Token::Char(op, _) = tk else {
            return Some(Ok(left));
        };

        if ADDITIVE_OPS.contains(&op.to_string().as_str()) {
            let _ = self.lexer.next_token();

            if op == '=' {
                if let Some(Ok(Token::Char(c, _))) = self.lexer.peek_next_token() {
                    if c == '=' {
                        let _ = self.lexer.next_token();

                        let Some(right) = self.parse_additive_expr() else {
                            return Some(Err(ParseError::UnexpectedEOF(
                                self.file.clone(),
                                "EXPRESSION".to_string(),
                            )));
                        };

                        return match right {
                            Ok(right) => Some(Ok(AstNode::InfixOp(
                                LineInfo::new(
                                    left.line_info().begin_char(),
                                    self.lexer.state().current_char,
                                    left.line_info().begin_line(),
                                    self.lexer.state().current_line,
                                ),
                                Rc::from(left),
                                "==".into(),
                                Rc::from(right),
                            ))),
                            Err(e) => Some(Err(e)),
                        };
                    }
                }
            }

            let Some(right) = self.parse_additive_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXPRESSION".to_string()
                )));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(LineInfo::new(
                        left.line_info().begin_char(),
                        self.lexer.state().current_char,
                        left.line_info().begin_line(),
                        self.lexer.state().current_line,
                    ), Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        Some(Ok(left))
    }

    pub fn parse_bitwise_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_comparative_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        for op in BITWISE_OPS {
            if self.expect_chars(op, true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                let Some(right) = self.parse_bitwise_expr() else {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "EXPRESSION".to_string()
                    )));
                };

                match right {
                    Ok(right) => {
                        left = AstNode::InfixOp(LineInfo::new(
                            left.line_info().begin_char(),
                            self.lexer.state().current_char,
                            left.line_info().begin_line(),
                            self.lexer.state().current_line,
                        ),Rc::from(left), op.to_string(), Rc::from(right))
                    }

                    Err(e) => return Some(Err(e)),
                }
            }
        }

        Some(Ok(left))
    }

    pub fn parse_comparative_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let mut left = match self.parse_additive_expr()? {
            Ok(left) => left,
            Err(e) => return Some(Err(e)),
        };

        let mut op = None;

        for operator in COMPARATIVE_OPS {
            if self.expect_chars(operator, true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                op = Some(operator);
                break
            }
        }

        if let Some(op) = op {
            let Some(right) = self.parse_comparative_expr() else {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXPRESSION".to_string()
                )));
            };

            match right {
                Ok(right) => {
                    left = AstNode::InfixOp(LineInfo::new(
                        left.line_info().begin_char(),
                        self.lexer.state().current_char,
                        left.line_info().begin_line(),
                        self.lexer.state().current_line,
                    ), Rc::from(left), op.to_string(), Rc::from(right))
                }

                Err(e) => return Some(Err(e)),
            }
        }

        if let Some(Ok(Token::Char(c, _))) = self.lexer.peek_next_token() {
            if c == '=' {
                let _ = self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line));

                let right = match self.next_ast_node()? {
                    Ok(left) => left,
                    Err(e) => return Some(Err(e)),
                };

                left = AstNode::InfixOp(LineInfo::new(
                    left.line_info().begin_char(),
                    self.lexer.state().current_char,
                    left.line_info().begin_line(),
                    self.lexer.state().current_line,
                ), Rc::new(left), "=".into(), Rc::new(right));
            }
        }

        Some(Ok(left))
    }

    pub fn parse_mut_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"mut", true).unwrap();

        let name = match self.lexer.next_token() {
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "MUT DEF NAME".to_string()
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Ident("MUT DEF NAME".to_string(), LineInfo::default()),
                    tk,
                )))
            }
        };

        if self.expect_chars(&":", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let def_type = match self.parse_type() {
                Ok(def_type) => def_type,
                Err(e) => return Some(Err(e)),
            };

            let _ = self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line));

            let value = match self.next_ast_node() {
                None => {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "MUT DEF VALUE (EXPR)".to_string()
                    )))
                }
                Some(Ok(node)) => node,
                Some(Err(e)) => return Some(Err(e)),
            };

            return Some(Ok(AstNode::MutStmt {
                name_info: LineInfo::new(
                    start.begin_char(),
                    value.line_info().end_char(),
                    start.begin_line(),
                    value.line_info().end_line(),
                ),
                name,
                def_type: Some(def_type),
                value: Rc::from(value),
            }));
        };

        let _ = self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line));

        let value = match self.next_ast_node() {
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "MUT DEF VALUE (EXPR)".to_string()
                )))
            }
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
        };

        Some(Ok(AstNode::MutStmt {
            name_info: LineInfo::new(
                start.begin_char(),
                value.line_info().end_char(),
                start.begin_line(),
                value.line_info().end_line(),
            ),
            name,
            def_type: None,
            value: Rc::from(value),
        }))
    }

    pub fn parse_let_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"let", true).unwrap();

        let name = match self.lexer.next_token() {
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "LET DEF VALUE (EXPR)".to_string()
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Ident("NAME".to_string(), LineInfo::default()),
                    tk,
                )))
            }
        };

        if self.expect_chars(&":", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            let def_type = match self.parse_type() {
                Ok(def_type) => def_type,
                Err(e) => return Some(Err(e)),
            };

            let _ = self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line));

            let value = match self.next_ast_node() {
                None => {
                    return Some(Err(ParseError::UnexpectedEOF(
                        self.file.clone(),
                        "LET DEF VALUE (EXPR)".to_string()
                    )))
                }
                Some(Ok(node)) => node,
                Some(Err(e)) => return Some(Err(e)),
            };

            return Some(Ok(AstNode::LetStmt {
                name_info: LineInfo::new(
                    start.begin_char(),
                    value.line_info().end_char(),
                    start.begin_line(),
                    value.line_info().end_line(),
                ),
                name,
                def_type: Some(def_type),
                value: Rc::from(value),
            }));
        };

        let _ = self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line));

        let value = match self.next_ast_node() {
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "LET DEF VALUE (EXPR)".to_string()
                )))
            }
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
        };

        Some(Ok(AstNode::LetStmt {
            name_info: LineInfo::new(
                start.begin_char(),
                value.line_info().end_char(),
                start.begin_line(),
                value.line_info().end_line(),
            ),
            name,
            def_type: None,
            value: Rc::from(value),
        }))
    }

    pub fn parse_include_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"include", true).unwrap();

        let (info, path) = match self.parse_path_expr(None) {
            Some(Ok(AstNode::Path(info, path))) => (info, path),
            Some(Ok(_)) => unreachable!(),
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "INCLUDE STMT PATH".to_string()
                )))
            }
        };

        Some(Ok(AstNode::IncludeStmt(LineInfo::new(
            start.begin_char(),
            info.end_char(),
            start.begin_line(),
            info.end_line(),
        ), path)))
    }

    pub fn parse_if_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"if", true).unwrap();

        let cond = match self.parse_comparative_expr() {
            Some(Ok(cond)) => cond,
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "IF COND".to_string()
                )))
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
                line_info: LineInfo::new(
                    start.begin_char(),
                    self.lexer.state().current_char,
                    start.begin_line(),
                    self.lexer.state().current_line,
                ),
                cond: Rc::from(cond),
                block: main_body,
                else_clause,
            }));
        }

        Some(Ok(AstNode::IfStmt {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            cond: Rc::from(cond),
            block: main_body,
        }))
    }

    pub fn parse_fn_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"fn", true).unwrap();

        let (name, of) = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, ..))) => {
                if self.expect_chars(&"::", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                    let p = &[
                        name,
                        match self.lexer.next_token() {
                            Some(Ok(Token::Ident(p2, _))) => p2,
                            _ => panic!(),
                        },
                    ];

                    assert_eq!(p.len(), 2); // TODO: Handle this error case properly

                    (p[1].clone(), Some(p[0].clone()))
                } else {
                    (name, None)
                }
            }
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Debug("FN_NAME".into()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "FUNCTION NAME".to_string()
                )))
            }
        };

        let tg_args = if self.expect_chars(&"<", false, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
            match self.parse_tg_list() {
                Ok(v) => v,
                Err(e) => return Some(Err(e)),
            }
        } else {
            Default::default()
        };

        let args = match self.parse_args_list(true) {
            Ok(args) => args.into_boxed_slice(),
            Err(e) => return Some(Err(e)),
        };

        let mut modifiers = vec![];

        while let Some(Ok(Token::Ident(m, _))) = self.lexer.peek_next_token() {
            let Ok(m) = Modifier::from_str(&*m) else {
                break;
            };

            modifiers.push(m);

            let _ = self.lexer.next_token();
        }

        match self.expect_chars(&"->", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
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

        Some(Ok(AstNode::FnStmt {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            of,
            name,
            ret_type,
            args,
            code,
            type_generics: tg_args,
            modifiers: modifiers.into_boxed_slice(),
        }))
    }

    pub fn parse_extern_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"extern", true).unwrap();

        let stmt = match self.lexer.peek_next_token() {
            Some(Ok(Token::Ident(s, _))) => s,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Debug("EXTERN_STMT".into()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXTERNAL STMT".to_string()
                )))
            }
        };

        match &*stmt {
            "fn" => self.parse_extern_fn_stmt(&start),
            stmt => unimplemented!("extern {stmt}s."),
        }
    }

    pub fn parse_extern_fn_stmt(&mut self, start: &LineInfo) -> Option<Result<AstNode, ParseError>> {
        let _ = self.expect_ident(&"fn", true);

        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, ..))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Debug("EXTERNAL FUNCTION NAME".into()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "EXTERNAL FUNCTION NAME".to_string()
                )))
            }
        };

        let args = match self.parse_args_list(true) {
            Ok(args) => args.into_boxed_slice(),
            Err(e) => return Some(Err(e)),
        };

        match self.expect_chars(&"->", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };

        let ret_type = match self.parse_type() {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::ExternFn {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            name,
            ret_type,
            args,
        }))
    }

    pub fn parse_return_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"return", true).unwrap();

        let value = match self.next_ast_node() {
            Some(Ok(node)) => node,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        Some(Ok(AstNode::ReturnStmt(LineInfo::new(
            start.begin_char(),
            value.line_info().end_char(),
            start.begin_line(),
            value.line_info().end_char(),
        ),Indirection::new(value))))
    }

    pub fn parse_for_in_expr(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"for", true).unwrap();

        let var = match self.lexer.next_token() {
            Some(Ok(Token::Ident(v, _))) => v,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Debug("FOR_IN_VAR".into()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "FOR {VAR} IN ...".to_string()
                )))
            }
        };

        let _ = self.expect_ident(&"in", true);

        let of = match self.next_ast_node()? {
            Err(e) => return Some(Err(e)),
            Ok(n) => n,
        };

        let block = match self.parse_block_expr() {
            Ok(b) => b,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::ForInStmt {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            var,
            of: Indirection::new(of),
            block,
        }))
    }

    pub fn parse_type_alias(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"type", true).unwrap();

        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Ident("".into(), LineInfo::default()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "TYPE ALIAS NAME".to_string()
                )))
            }
        };

        match self.expect_chars(&"=", true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)) {
            Err(e) => return Some(Err(e)),
            Ok(_) => (),
        };

        let ty = match self.parse_type() {
            Ok(ty) => ty,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::TypeAlias(LineInfo::new(
            start.begin_char(),
            self.lexer.state().current_char,
            start.begin_line(),
            self.lexer.state().current_line,
        ),name, ty)))
    }

    pub fn parse_macro_def(&mut self) -> Option<Result<AstNode, ParseError>> {
        let _ = self.expect_ident(&"macro", true);

        if let Err(e) = self.expect_char(&'@', true) {
            return Some(Err(e));
        }

        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => return Some(Err(ParseError::ExpectedToken(self.file.clone(), Token::Debug("MACRO NAME".into()), tk))),
            Some(Err(e)) => return Some(Err(e)),
            None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "MACRO NAME".to_string())))
        };

        if let Err(e) = self.expect_char(&'(', true) {
            return Some(Err(e));
        }
        
        let mut macro_def = Macro {
            arguments: Default::default(),
        };
        
        while let Ok(_) = self.expect_char(&'$', true) {
            let name = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => return Some(Err(ParseError::ExpectedToken(self.file.clone(), Token::Debug("MACRO_ARG_NAME".into()), tk))),
                Some(Err(e)) => return Some(Err(e)),
                None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "MACRO PARAMETER NAME".to_string())))
            };

            if let Err(e) = self.expect_char(&':', true) {
                return Some(Err(e));
            }
            
            let kind = match self.lexer.next_token() {
                Some(Ok(Token::Ident(name, _))) => name,
                Some(Ok(tk)) => return Some(Err(ParseError::ExpectedToken(self.file.clone(), Token::Debug("MACRO_ARG_NAME".into()), tk))),
                Some(Err(e)) => return Some(Err(e)),
                None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "MACRO PARAMETER NAME".to_string())))
            };
            
            let kind = match MacroArgKind::from_str(&self.file, &name, &kind) {
                Ok(kind) => kind,
                Err(e) => return Some(Err(e))
            };
            
            macro_def.arguments.insert(name, kind);
        }

        if let Err(e) = self.expect_char(&')', true) {
            return Some(Err(e));
        }
        
        self.macros.insert(name, macro_def);

        self.next_ast_node()
    }
    
    pub fn parse_defer_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"defer", true).unwrap();
        
        let block = if self.expect_char(&'{', false).is_ok() {
            match self.parse_block_expr() {
                Err(e) => return Some(Err(e)),
                Ok(block) => block,
            }
        } else {
            let node = match self.next_ast_node() {
                Some(Ok(node)) => node,
                Some(Err(e)) => return Some(Err(e)),
                None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "DEFER CODE".to_string())))
            };
            
            ParseBlock::Plain(Box::new([node]))
        };
        
        Some(Ok(AstNode::DeferStmt(LineInfo::new(
            start.begin_char(),
            self.lexer.state().current_char,
            start.begin_line(),
            self.lexer.state().current_line,
        ), block)))
    }

    pub fn parse_match_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"match", true).unwrap();

        let matchee = match self.parse_bitwise_expr() {
            None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "MATCHEE".to_string()))),
            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(matchee)) => matchee,
        };
        
        match self.expect_char(&'{', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };
        
        let mut arms = vec![];
        
        while self.expect_char(&'}', true).is_err() {
            if self.expect_ident(&"else", true).is_ok() {
                let block = match self.parse_block_expr() {
                    Ok(block) => block,
                    Err(e) => return Some(Err(e)),
                };

                arms.push(MatchArm {
                    operator: "".to_string(),
                    // TODO: fix this
                    right: Indirection::new(AstNode::NullLiteral(LineInfo::default())),
                    is_else: true,
                    code: block,
                });
                
                break
            }

            let mut operator = "==".to_string();

            for op in MATCH_OPS {
                if self.expect_chars(op, true, &LineInfo::new_one_char(self.lexer.state().current_char, self.lexer.state().current_line)).is_ok() {
                    operator = op.to_string();
                    break
                }
            }

            let right = match self.parse_multiplicative_expr() {
                None => return Some(Err(ParseError::UnexpectedEOF(self.file.clone(), "MATCHEE".to_string()))),
                Some(Err(e)) => return Some(Err(e)),
                Some(Ok(right)) => right,
            };

            /*match self.expect_chars(&"->", true) {
                Ok(_) => (),
                Err(e) => return Some(Err(e)),
            };*/

            let block = match self.parse_block_expr() {
                Ok(block) => block,
                Err(e) => return Some(Err(e)),
            };

            arms.push(MatchArm {
                operator,
                right: Indirection::new(right),
                is_else: false,
                code: block,
            })
        }

        match self.expect_char(&'}', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };
        
        Some(Ok(AstNode::MatchExpr {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            matchee: Rc::new(matchee),
            arms: arms.into(),
        }))
    }

    pub fn parse_data_stmt(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"data", true).unwrap();

        let name = match self.lexer.next_token() {
            Some(Ok(Token::Ident(name, _))) => name,
            Some(Ok(tk)) => {
                return Some(Err(ParseError::ExpectedToken(
                    self.file.clone(),
                    Token::Ident("".into(), LineInfo::default()),
                    tk,
                )))
            }
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "DATA STMT NAME".to_string()
                )))
            }
        };

        match self.expect_char(&'{', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };

        let mut fields: Vec<(bool, String, ParseType)> = vec![];

        while self.expect_ident(&"let", false).is_ok() || self.expect_ident(&"mut", false).is_ok() {
            if self.expect_ident(&"let", true).is_ok() {
                let name = match self.lexer.next_token() {
                    Some(Ok(Token::Ident(name, _))) => name,
                    Some(Ok(tk)) => {
                        return Some(Err(ParseError::ExpectedToken(
                            self.file.clone(),
                            Token::Ident("".into(), LineInfo::default()),
                            tk,
                        )))
                    }
                    Some(Err(e)) => return Some(Err(e)),
                    None => {
                        return Some(Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "DATA FIELD NAME".to_string()
                        )))
                    }
                };

                match self.expect_char(&':', true) {
                    Ok(_) => (),
                    Err(e) => return Some(Err(e)),
                }

                let ty = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Some(Err(e)),
                };

                fields.push((false, name, ty));
            } else if self.expect_ident(&"mut", true).is_ok() {
                let name = match self.lexer.next_token() {
                    Some(Ok(Token::Ident(name, _))) => name,
                    Some(Ok(tk)) => {
                        return Some(Err(ParseError::ExpectedToken(
                            self.file.clone(),
                            Token::Ident("".into(), LineInfo::default()),
                            tk,
                        )))
                    }
                    Some(Err(e)) => return Some(Err(e)),
                    None => {
                        return Some(Err(ParseError::UnexpectedEOF(
                            self.file.clone(),
                            "DATA FIELD NAME".to_string()
                        )))
                    }
                };

                match self.expect_char(&':', true) {
                    Ok(_) => (),
                    Err(e) => return Some(Err(e)),
                }

                let ty = match self.parse_type() {
                    Ok(t) => t,
                    Err(e) => return Some(Err(e)),
                };

                fields.push((true, name, ty));
            }
        }

        match self.expect_char(&'}', true) {
            Ok(_) => (),
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::DataStmt {
            name,
            fields,
            modifiers: vec![],
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
        }))
    }

    pub fn parse_guard_clause(&mut self) -> Option<Result<AstNode, ParseError>> {
        let start = self.expect_ident(&"guard", true).unwrap();

        let cond = match self.parse_bitwise_expr() {
            Some(Ok(cond)) => cond,
            Some(Err(e)) => return Some(Err(e)),
            None => {
                return Some(Err(ParseError::UnexpectedEOF(
                    self.file.clone(),
                    "GUARD COND".to_string()
                )))
            }
        };

        self.expect_ident(&"else", true).unwrap();

        let else_code = match self.parse_block_expr() {
            Ok(block) => block,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(AstNode::GuardClause {
            line_info: LineInfo::new(
                start.begin_char(),
                self.lexer.state().current_char,
                start.begin_line(),
                self.lexer.state().current_line,
            ),
            cond: Indirection::new(cond),
            else_code,
        }))
    }

    pub fn next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        if let Some(Ok(Token::Ident(ident, _))) = self.lexer.peek_next_token() {
            match ident.as_str() {
                "macro" => self.parse_macro_def(),
                "data" => self.parse_data_stmt(),
                "let" => self.parse_let_stmt(),
                "mut" => self.parse_mut_stmt(),
                "include" => self.parse_include_stmt(),
                "if" => self.parse_if_expr(),
                "fn" => self.parse_fn_expr(),
                "extern" => self.parse_extern_stmt(),
                "return" => self.parse_return_stmt(),
                "for" => self.parse_for_in_expr(),
                "type" => self.parse_type_alias(),
                "defer" => self.parse_defer_stmt(),
                "match" => self.parse_match_stmt(),
                "guard" => self.parse_guard_clause(),
                _ => self.parse_bitwise_expr(),
            }
        } else if let Some(Ok(Token::Char(c, _))) = self.lexer.peek_next_token() {
            match c {
                ';' => {
                    self.lexer.next_token();
                    self.next_ast_node()
                },
                _ => self.parse_bitwise_expr(),
            }
        } else {
            self.parse_bitwise_expr()
        }
    }

    pub fn peek_next_ast_node(&mut self) -> Option<Result<AstNode, ParseError>> {
        let prev_state = self.state();

        let node = self.next_ast_node();

        self.reset_to_state(prev_state);

        node
    }
}
