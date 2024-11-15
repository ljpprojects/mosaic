use crate::file::File;
use std::marker::PhantomData;
use std::mem;
use std::rc::Rc;

pub trait WithState {
    type ToState: State;

    fn from_state(state: Self::ToState) -> Self;
    fn reset_to_state(&mut self, state: Self::ToState);
    fn state(&self) -> Self::ToState;
}

pub trait State {}

pub struct ReaderState {
    pub pos: u64,
    pub reader: Rc<File<String>>,
}

impl State for ReaderState {}

impl ReaderState {
    pub fn new(reader: Rc<File<String>>, pos: u64) -> ReaderState {
        ReaderState { pos, reader }
    }
}

pub struct LexerState {
    pub reader_state: ReaderState,
    pub pos: u64,
    pub current_char: usize,
    pub current_line: usize,
    pub is_first: bool,
}

impl State for LexerState {}

impl LexerState {
    pub fn new(
        reader_state: ReaderState,
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

pub struct ParserState {
    pub lexer_state: LexerState,
}

impl State for ParserState {}

impl ParserState {
    pub fn new(lexer_state: LexerState) -> Self {
        Self { lexer_state }
    }
}
