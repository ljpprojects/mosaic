#![allow(clippy::unwrap_used)]

use crate::file::File;
use crate::states::{ReaderState, WithState};
use crate::tokens::LineInfo;
use cranelift_object::object::ReadRef;
use mmap_rs::{Mmap, MmapOptions};

use std::rc::Rc;
use std::{fs, io};

#[derive(Debug)]
pub struct CharReader {
    pub(crate) reader: File<String>,
    pub pos: u64,
    mmap: Mmap,
}

impl PartialEq for CharReader {
    fn eq(&self, other: &Self) -> bool {
        self.reader.clone() == other.reader.clone() && self.pos == other.pos
    }
}

impl Clone for CharReader {
    fn clone(&self) -> Self {
        let file_length = fs::metadata(self.reader.path()).unwrap().len() as usize;
        let mmap = unsafe { MmapOptions::new(file_length).unwrap().with_file(&self.reader.file(), 0) }.map().unwrap();

        Self {
            reader: self.reader.clone(),
            pos: self.pos,
            mmap,
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
        let file_length = std::fs::metadata(reader.path()).unwrap().len() as usize;
        let mmap = unsafe { MmapOptions::new(file_length).unwrap().with_file(&reader.file(), 0) }.map().unwrap();

        Self { reader, pos: 0, mmap }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let byte = *self.mmap.read_at::<u8>(self.pos).ok()?;

        self.pos += 1;

        Some(byte as char)
    }

    pub fn peek_next_char(&self) -> Option<char> {
        Some(*self.mmap.read_at::<u8>(self.pos).ok()? as char)
    }

    pub fn get_snippet(&self, info: &LineInfo) -> io::Result<String> {
        let mut snippet = String::new();

        let mut offset = 0;
        let buf = String::from_utf8(self.mmap.read_slice(&mut offset, self.mmap.len()).unwrap().to_vec()).unwrap();
        let lines = buf.lines().collect::<Vec<_>>();

        for (linec, line) in lines.into_iter().enumerate() {
            if linec + 1 < info.begin_line() {
                continue
            }

            if linec + 1 > info.end_line() {
                break
            }

            for (charc, char) in line.chars().enumerate() {
                if charc + 1 < info.begin_char() && linec + 1 == info.begin_line() {
                    continue
                }

                if charc + 1 > info.end_char() && linec + 1 == info.end_line() {
                    break
                }

                snippet.push(char);
            }

            snippet.push('\n');
        }

        Ok(snippet)
    }
}