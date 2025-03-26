use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

#[derive(PartialEq, Clone, Copy, Hash, Eq, Ord, PartialOrd)]
pub struct LineInfo {
    start_char: usize,
    end_char: usize,
    start_line: usize,
    end_line: usize,
}

impl Default for LineInfo {
    fn default() -> Self {
        LineInfo::new_one_char(
            1,
            1
        )
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
    pub fn new(
        start_char: usize,
        end_char: usize,
        start_line: usize,
        end_line: usize,
    ) -> LineInfo {
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

#[derive(Debug, Clone)]
pub enum Token {
    Char(char, LineInfo),
    String(String, LineInfo),
    Ident(String, LineInfo),
    Number(f64, LineInfo),
    /// a char literal
    Byte(u8, LineInfo),
    Debug(String),
}

impl Token {
    pub fn line_info(&self) -> LineInfo {
        match self {
            Token::Char(_, info) => info.clone(),
            Token::String(_, info) => info.clone(),
            Token::Ident(_, info) => info.clone(),
            Token::Number(_, info) => info.clone(),
            Token::Debug(_) => LineInfo::default(),
            Token::Byte(_, info) => info.clone(),
        }
    }
}
