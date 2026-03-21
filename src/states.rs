use crate::file::File;
use crate::parser::Macro;
use crate::reader::CharReader;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub offset: usize,
    pub line: u32,
    pub column: u32,
}

impl Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}) {}:{}", self.offset, self.column, self.line)
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.column, self.line)
    }
}

pub trait WithState {
    type ToState: State;

    fn from_state(state: Self::ToState) -> Self;
    fn reset_to_state(&mut self, state: Self::ToState);
    fn state(&self) -> Self::ToState;
}

pub trait State {}

#[derive(Debug)]
pub struct ReaderState<'a> {
    pub pos: u64,
    pub path: &'a str,
}

impl State for ReaderState<'_> {}

impl<'a> ReaderState<'a> {
    pub fn new(path: &'a str, pos: u64) -> ReaderState {
        ReaderState { pos, path }
    }
}

#[derive(Debug)]
pub struct LexerState<'a> {
    pub reader_state: ReaderState<'a>,
    pub pos: Position,
    pub is_first: bool,
}

impl State for LexerState<'_> {}

impl<'a> LexerState<'a> {
    pub fn new(
        reader_state: ReaderState<'a>,
        pos: u64,
        current_char: usize,
        current_line: usize,
        is_first: bool,
    ) -> Self {
        Self {
            reader_state,
            pos,
            current_char,
            current_line,
            is_first,
        }
    }
}

#[derive(Debug)]
pub struct ParserState<'a> {
    pub lexer_state: LexerState<'a>,
}

impl State for ParserState<'_> {}

impl<'a> ParserState<'a> {
    pub fn new(lexer_state: LexerState<'a>) -> Self {
        Self { lexer_state }
    }
}
