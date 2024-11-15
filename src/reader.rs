#![forbid(unsafe_code)]

use crate::file::File;
use crate::states::{ReaderState, WithState};
use std::os::unix::fs::FileExt;
use std::rc::Rc;

#[derive(Debug)]
pub struct CharReader {
    reader: File<String>,
    pub pos: u64,
}

impl Clone for CharReader {
    fn clone(&self) -> Self {
        Self {
            reader: self.reader.clone(),
            pos: self.pos,
        }
    }
}

impl WithState for CharReader {
    type ToState = ReaderState;

    fn from_state(state: Self::ToState) -> Self {
        Self::new(state.reader.as_ref().clone())
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        let reader = state.reader.as_ref().clone();

        self.reader = reader;
    }

    fn state(&self) -> Self::ToState {
        ReaderState::new(Rc::from(self.reader.clone()), self.pos)
    }
}

impl CharReader {
    pub fn new(reader: File<String>) -> Self {
        Self { reader, pos: 0 }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let mut binding = [0u8; 1];
        let mut buf = binding.as_mut();

        self.reader.file().read_exact_at(&mut buf, self.pos).ok()?;

        self.pos += 1;

        Some(buf[0] as char)
    }

    pub fn peek_next_char(&self) -> Option<char> {
        let mut binding = [0u8; 1];
        let mut buf = binding.as_mut();

        self.reader.file().read_exact_at(&mut buf, self.pos).ok()?;

        Some(buf[0] as char)
    }
}
