use crate::file::File;
use crate::states::{ReaderState, WithState};
use mmap_rs::{Mmap, MmapFlags, MmapOptions};

use std::fs;

#[derive(Debug)]
pub struct CharReader<'a> {
    pub pos: usize,
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

    pub fn static_bytes(bytes: Box<[u8]>) -> Self {
        let mut mmap =
            MmapOptions::new(bytes.len())
                .unwrap()
                .with_flags(MmapFlags::SEQUENTIAL)
                .map_mut()
                .unwrap();

        mmap.copy_from_slice(&*bytes);

        Self {
            path: "-",
            pos: 0,
            mmap: mmap.make_read_only().unwrap(),
        }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let byte = *self.mmap.get(self.pos)?;

        self.pos += 1;

        Some(byte as char)
    }

    pub fn prev_char(&mut self) -> Option<char> {
        self.pos -= 1;

        let byte = *self.mmap.get(self.pos)?;
        Some(byte as char)
    }

    pub fn peek_next_char(&self) -> Option<char> {
        self.mmap.get(self.pos).map(|&c| c as char)
    }
}
