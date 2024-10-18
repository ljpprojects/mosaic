use std::os::unix::fs::FileExt;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CharReader<R>
where R: FileExt {
    reader: R,
    pub pos: u64,
}

impl<R: FileExt> CharReader<R> {
    pub(crate) fn new(reader: R) -> Self {
        Self {
            reader,
            pos: 0,
        }
    }

    pub fn next_char(&mut self) -> Option<char> {
        let mut binding = [0u8; 1];
        let mut buf = binding.as_mut();

        self.reader.read_exact_at(&mut buf, self.pos).ok()?;

        self.pos += 1;

        Some(buf[0] as char)
    }

    pub fn reset(&mut self) {
        self.pos = 0;
    }

    pub fn peek_next_char(&mut self) -> Option<char> {
        let mut binding = [0u8; 1];
        let mut buf = binding.as_mut();

        self.reader.read_exact_at(&mut buf, self.pos).ok()?;

        Some(buf[0] as char)
    }
}
