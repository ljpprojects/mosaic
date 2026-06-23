use crate::debug::TokenContext;
use std::fmt::{Debug, Display};
use std::num::{NonZeroU8, NonZeroU16};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub offset: u16,
    pub line: NonZeroU16,
    pub column: NonZeroU8,
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

#[derive(Debug, Clone, Copy)]
pub struct ReaderState<'a> {
    pub pos: usize,
    pub path: &'a str,
}

impl State for ReaderState<'_> {}

impl<'a> ReaderState<'a> {
    pub fn new(path: &'a str, pos: usize) -> ReaderState {
        ReaderState { pos, path }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LexerState<'a> {
    pub reader_state: ReaderState<'a>,
    pub pos: Position,
    pub cur_context: Option<TokenContext>,
}

impl State for LexerState<'_> {}

impl<'a> LexerState<'a> {
    pub fn new(
        reader_state: ReaderState<'a>,
        pos: Position,
        cur_context: Option<TokenContext>,
    ) -> Self {
        Self {
            reader_state,
            pos,
            cur_context
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
