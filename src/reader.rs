#![forbid(unsafe_code)]

use crate::file::File;
use crate::states::{ReaderState, WithState};
use crate::tokens::LineInfo;
use std::io::Read;
use std::os::unix::fs::FileExt;
use std::rc::Rc;
use std::{fs, io};

#[derive(Debug, PartialEq)]
pub struct CharReader {
    pub(crate) reader: File<String>,
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

    // TODO: Support multi-line snippets
    pub fn get_snippet(&self, info: &LineInfo) -> io::Result<String> {
        let mut buf = vec![];
        let mut snippet = String::new();

        let mut file = fs::File::open(self.reader.path().to_string_lossy().to_string())?;

        file.read_to_end(&mut buf)?;

        let buf = String::from_utf8(buf).unwrap();
        let lines = buf.lines().collect::<Vec<_>>();

        for (i, line) in lines.iter().enumerate() {
            if i < info.begin_line() - 1 {
                continue;
            }

            if i >= info.end_line() {
                break;
            }

            for (i, char) in line.to_string().chars().enumerate() {
                if i < info.begin_char() - 1 {
                    continue;
                }

                if i >= info.end_char() - 1 {
                    break;
                }

                snippet.push(char);
            }
        }

        Ok(snippet)
    }
}