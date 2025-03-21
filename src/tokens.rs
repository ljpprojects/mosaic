use crate::utils::{Indirection, IndirectionTrait};
use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;
use std::rc::Rc;

#[derive(PartialEq)]
pub struct LineInfo {
    start_char: Rc<usize>,
    end_char: Rc<usize>,
    start_line: Rc<usize>,
    end_line: Rc<usize>,
}

impl Clone for LineInfo {
    fn clone(&self) -> Self {
        LineInfo::new(
            self.start_char.clone(),
            self.end_char.clone(),
            self.start_line.clone(),
            self.end_line.clone(),
        )
    }
}

impl Default for LineInfo {
    fn default() -> Self {
        LineInfo::new_one_char(
            Indirection::new(1),
            Indirection::new(1),
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
        start_char: Rc<usize>,
        end_char: Rc<usize>,
        start_line: Rc<usize>,
        end_line: Rc<usize>,
    ) -> LineInfo {
        LineInfo {
            start_char,
            end_char,
            start_line,
            end_line,
        }
    }

    pub fn new_one_char(char: Indirection<usize>, line: Indirection<usize>) -> LineInfo {
        LineInfo {
            start_char: char.clone().into(),
            end_char: char.map(|n| n + 1).into(),
            start_line: line.clone().into(),
            end_line: line.into(),
        }
    }

    pub fn to_ranges(&self) -> (Range<usize>, Range<usize>) {
        (
            *self.start_char..*self.end_char,
            *self.start_line..*self.end_line,
        )
    }

    pub fn begin_line(&self) -> usize {
        *self.start_line
    }

    pub fn end_line(&self) -> usize {
        *self.end_line
    }

    pub fn begin_char(&self) -> usize {
        *self.start_char
    }

    pub fn end_char(&self) -> usize {
        *self.end_char
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
