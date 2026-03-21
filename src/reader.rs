use crate::file::File;
use crate::states::{ReaderState, WithState};
use crate::tokens::LineInfo;
use cranelift_object::object::ReadRef;
use mmap_rs::{Mmap, MmapOptions, UnsafeMmapFlags};

use std::borrow::Cow;
use std::rc::Rc;
use std::{fs, io};

#[derive(Debug)]
pub struct CharReader<'a> {
    pub pos: u64,
    pub path: &'a str,
    mmap: Mmap,
}

impl PartialEq for CharReader<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.mmap.as_ref() == other.mmap.as_ref()
    }
}

impl<'a> Clone for CharReader<'a> {
    fn clone(&self) -> Self {
        Self::open(self.path)
    }
}

impl<'a> WithState for CharReader<'a> {
    type ToState = ReaderState<'a>;

    fn from_state(state: Self::ToState) -> Self {
        Self::open(state.path)
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        self.path = state.path;
        self.pos = state.pos;
    }

    fn state(&self) -> Self::ToState {
        ReaderState::new(self.path, self.pos)
    }
}

impl<'a> CharReader<'a> {
    pub fn open(path: &'a str) -> Self {
        let file_length = fs::metadata(path).unwrap().len() as usize;
        let file = File::new(path.to_owned()).unwrap();

        let mmap = unsafe {
            MmapOptions::new(file_length)
                .unwrap()
                .with_file(file.file(), 0)
        }
        .map()
        .unwrap();

        Self { path, pos: 0, mmap }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let byte = *self.mmap.read_at::<u8>(self.pos).ok()?;

        self.pos += 1;

        Some(byte as char)
    }

    pub fn peek_next_char(&self) -> Option<char> {
        self.mmap.read_at::<u8>(self.pos).ok().map(|&c| c as char)
    }

    pub fn get_snippet(&self, info: &LineInfo) -> io::Result<String> {
        let mut snippet = String::new();

        let mut offset = 0;
        let buf = String::from_utf8(
            self.mmap
                .read_slice(&mut offset, self.mmap.len())
                .unwrap()
                .to_vec(),
        )
        .unwrap();

        let lines = buf.lines().collect::<Vec<_>>();

        for (linec, line) in lines.into_iter().enumerate() {
            if linec + 1 < info.begin_line() {
                continue;
            }

            if linec + 1 > info.end_line() {
                break;
            }

            for (charc, char) in line.chars().enumerate() {
                if charc + 1 < info.begin_char() && linec + 1 == info.begin_line() {
                    continue;
                }

                if charc + 1 > info.end_char() && linec + 1 == info.end_line() {
                    break;
                }

                snippet.push(char);
            }

            snippet.push('\n');
        }

        Ok(snippet)
    }
}
