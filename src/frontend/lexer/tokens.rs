use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

use bigdecimal::BigDecimal;

use crate::frontend::lexer::debug::PositionRange;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringEscape {
    Newline,
    CarriageReturn,
    Backspace,
    Null,
    Tab,
    /// equivalent to \x1B
    /// Its primary use is for ANSI escapes, where you could have \e[31m for red text, however the
    Escape,
    Backslash,
    Apostrophe,
    DoubleQuote,

    /// Can be formatted as hex (\xHH), octal (\oNNN), or base-10 (\bNNN)
    Byte(u8),

    /// \u{HHHH} or \u{HHHHHH}
    UnicodeCharacter(char),

    /// Equivalent to \e[38;2;{R};{G};{B}m
    /// Syntax is \rgb(fg; {R},{G},{B})
    ANSIRGBFG(u8, u8, u8),

    /// Equivalent to \e[48;2;{R};{G};{B}m
    /// Syntax is \rgb(bg; {R},{G},{B})
    ANSIRGBBG(u8, u8, u8),

    /// Equivalent to \e[38;5;{C}m
    /// Syntax is \code(fg; {C})
    ANSICodeFG(u8),

    /// Equivalent to \e[48;5;{C}m
    /// Syntax is \code(bg; {C})
    ANSICodeBG(u8),

    /// Equivalent to \e[1m
    /// Syntax is \bold
    ANSIBold,

    /// Equivalent to \e[0m
    /// Syntax is \reset
    ANSIResetAll,

    /// Equivalent to \e[{Arg1};{Arg2};{...};{ArgN}m
    /// Syntax is \ansi({Arg1}; {Arg2}; {...}; {ArgN})
    ANSIOther(Box<[u8]>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StringPart {
    Static(String),
    Template(Box<[Token]>),
    Escape(StringEscape),
}

#[derive(Debug, Clone, PartialEq)]
pub struct StringInnards {
    pub parts: Box<[(StringPart, PositionRange)]>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    String(StringInnards),
    Character(char),
    Ident(String),
    Path(Vec<String>),
    Keyword(&'static str),
    Modifier(&'static str),
    Integer(u128),
    Decimal(BigDecimal),
    Symbol(char),
    LeftSlimArrow,
    RightSlimArrow,
    LeftThickArrow,
    RightThickArrow,
}
