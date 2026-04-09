use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

use bigdecimal::BigDecimal;

use crate::frontend::lexer::debug::PositionRange;
use crate::frontend::lexer::string::LEGAL_ESCAPE_SEQUENCES;

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

    /// Can be formatted as hex (\xHH) or octal (\oNNN)
    Byte(u8),

    /// \u{HHHH}
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

    /// Equivalent to \e[{Arg1};{Arg2};{...};{ArgN}{C}
    /// Syntax is \ansi({C}: {Arg1}; {Arg2}; {...}; {ArgN})
    ///
    /// A valid Arg matches the regex /[0-9]+/
    /// A valid C matches the regex /[a-zA-Z]/
    ///
    /// For example, \ansi(m: 48; 5; 15) is the equivalent of \code(bg; 15)
    ANSIOther(char, Box<[u8]>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StringPart {
    Static(String),
    Template(Box<[Token]>),
    Escape(StringEscape),
}

impl StringEscape {
    /// Tries to create a StringEscape from an escape sequence.
    /// If the escape sequence is invalid, None is returned.
    /// If the matched escape sequence is parameterised, None is returned.
    pub fn try_from_escape_seq(seq: &str) -> Option<Self> {
        let _guard = LEGAL_ESCAPE_SEQUENCES.binary_search(&seq).ok()?;

        match seq {
            "\"" => Some(StringEscape::DoubleQuote),
            "'" => Some(StringEscape::Apostrophe),
            "0" => Some(StringEscape::Null),
            "\\" => Some(StringEscape::Backslash),
            "ansi" | "bold" | "code" | "reset" | "rgb" | "o" | "u" | "x" => None,
            "b" => Some(StringEscape::Backspace),
            "e" => Some(StringEscape::Escape),
            "n" => Some(StringEscape::Newline),
            "r" => Some(StringEscape::CarriageReturn),
            "t" => Some(StringEscape::Tab),
            _ => unreachable!(),
        }
    }
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
    Integer(i128),
    Decimal(BigDecimal),
    Symbol(char),
    LeftSlimArrow,
    RightSlimArrow,
    LeftThickArrow,
    RightThickArrow,
}
