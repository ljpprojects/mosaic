use crate::file::File;
use crate::states::{ReaderState, WithState};
use mmap_rs::{Mmap, MmapFlags, MmapOptions};

use core::slice;
use std::{fs, str};

#[derive(Debug)]
pub struct CharReader<'a> {
    pub pos: usize,
    pub path: &'a str,
    _mmap: Mmap,
    mmaped_str: &'a str,
}

impl PartialEq for CharReader<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.pos == other.pos && self.path == other.path
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

        let mmaped_str =
            unsafe { str::from_utf8(slice::from_raw_parts(mmap.as_ptr(), mmap.len())).unwrap() };

        Self {
            path,
            pos: 0,
            _mmap: mmap,
            mmaped_str,
        }
    }

    pub fn static_bytes(bytes: Box<[u8]>) -> Self {
        let mut mmap = MmapOptions::new(bytes.len())
            .unwrap()
            .with_flags(MmapFlags::SEQUENTIAL)
            .map_mut()
            .unwrap();

        mmap.copy_from_slice(&*bytes);

        let mmap = mmap.make_read_only().unwrap();
        let mmaped_str =
            unsafe { str::from_utf8(slice::from_raw_parts(mmap.as_ptr(), mmap.len())).unwrap() };

        Self {
            path: "-",
            pos: 0,
            _mmap: mmap,
            mmaped_str,
        }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let c = self.mmaped_str.chars().nth(self.pos)?; // O(n) time; yuck, but before we were just getting the nth byte and casting it up to a character

        self.pos += 1;
        Some(c)
    }

    pub fn prev_char(&mut self) -> Option<char> {
        self.pos -= 1;

        let byte = self.mmaped_str.chars().nth(self.pos)?;
        Some(byte as char)
    }

    pub fn peek_next_char(&self) -> Option<char> {
        self.mmaped_str.chars().nth(self.pos)
    }
}
