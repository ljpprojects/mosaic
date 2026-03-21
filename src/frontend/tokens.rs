use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

use bigdecimal::BigDecimal;

#[derive(PartialEq, Clone, Copy, Hash, Eq, Ord, PartialOrd)]
pub struct LineInfo {
    start_char: usize,
    end_char: usize,
    start_line: usize,
    end_line: usize,
}

impl Default for LineInfo {
    fn default() -> Self {
        LineInfo::new_one_char(1, 1)
    }
}

impl Display for LineInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{} - {}:{}",
            self.start_line, self.start_char, self.end_line, self.end_char
        )
    }
}

impl Debug for LineInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{} - {}:{}",
            self.start_line, self.start_char, self.end_line, self.end_char
        )
    }
}

impl LineInfo {
    pub fn new(start_char: usize, end_char: usize, start_line: usize, end_line: usize) -> LineInfo {
        LineInfo {
            start_char,
            end_char,
            start_line,
            end_line,
        }
    }

    pub fn new_one_char(char: usize, line: usize) -> LineInfo {
        LineInfo {
            start_char: char,
            end_char: char,
            start_line: line,
            end_line: line,
        }
    }

    pub fn to_ranges(&self) -> (Range<usize>, Range<usize>) {
        (
            self.start_char..self.end_char,
            self.start_line..self.end_line,
        )
    }

    pub fn begin_line(&self) -> usize {
        self.start_line
    }

    pub fn end_line(&self) -> usize {
        self.end_line
    }

    pub fn begin_char(&self) -> usize {
        self.start_char
    }

    pub fn end_char(&self) -> usize {
        self.end_char
    }
}

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
    pub parts: Box<[StringPart]>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    String(StringInnards),
    Character(String),
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
