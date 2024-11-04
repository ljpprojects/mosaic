use std::fmt::{Debug, Display, Formatter};
use std::num::{NonZero, NonZeroUsize};
use std::rc::Rc;

#[derive(PartialEq)]
pub struct LineInfo {
    start_char: Rc<NonZero<usize>>,
    end_char: Rc<NonZero<usize>>,
    start_line: Rc<NonZero<usize>>,
    end_line: Rc<NonZero<usize>>,
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
            Rc::from(NonZeroUsize::new(1).unwrap()),
            Rc::from(NonZeroUsize::new(1).unwrap()),
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
        start_char: Rc<NonZero<usize>>,
        end_char: Rc<NonZero<usize>>,
        start_line: Rc<NonZero<usize>>,
        end_line: Rc<NonZero<usize>>,
    ) -> LineInfo {
        LineInfo {
            start_char,
            end_char,
            start_line,
            end_line,
        }
    }

    pub fn new_one_char(char: Rc<NonZero<usize>>, line: Rc<NonZero<usize>>) -> LineInfo {
        LineInfo {
            start_char: char.clone(),
            end_char: char,
            start_line: line.clone(),
            end_line: line,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Token {
    Char(char, LineInfo),
    String(String, LineInfo),
    Ident(String, LineInfo),
    Number(f64, LineInfo),
}

impl Token {
    pub fn line_info(&self) -> LineInfo {
        match self {
            Token::Char(_, info) => info.clone(),
            Token::String(_, info) => info.clone(),
            Token::Ident(_, info) => info.clone(),
            Token::Number(_, info) => info.clone(),
        }
    }
}
