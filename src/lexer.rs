use crate::errors::CompilationError;
use crate::reader::CharReader;
use crate::states::{LexerState, WithState};
use crate::tokens::{LineInfo, Token};
use std::cell::{Cell, RefCell};
use std::path::PathBuf;
use std::str::FromStr;

pub const VALID_CHARS: &[char] = &[
    '+', '-', '*', '/', '%',
    '^', ':', '?', '!', '=',
    '>', '<', '{', '}', '[',
    ']', '(', ')', '@', ',',
    '&', '|', '.', '$', ';',
];

/// This is equal to amount spaces a tab character is equal to.
/// This is important because without it the character position system does not work.
/// Can be overridden via the config key 'formatting.tab_space_count', or the '--tab-space-count' option.
///
/// `mosaic-lang build file.msc --tab-space-count 2`
/// or
///
/// **config.toml**
/// ```toml
/// [formatting]
/// tab_space_count = 2
/// ```
pub const TAB_SPACES_COUNT: u8 = 4;

pub fn is_mosaic_ident_start(c: &char) -> bool {
    c.is_alphabetic() || ['_', '$'].contains(c)
}

pub fn is_mosaic_ident_part(c: &char) -> bool {
    c.is_alphanumeric() || ['_', '$'].contains(c)
}

type LexError = CompilationError;

/// This is the lexer for the Mosaic programming language.
/// Like the CharReader struct, it returns tokens individually, allowing for better performance,
/// especially for large files.
#[derive(Debug, PartialEq)]
pub struct StreamedLexer {
    pub(crate) reader: CharReader,
    file: PathBuf,
    pos: u64,
    current_char: usize,
    current_line: usize,
    is_first: bool,
}

impl Clone for StreamedLexer {
    fn clone(&self) -> Self {
        StreamedLexer {
            reader: self.reader.clone(),
            file: self.file.clone(),
            pos: self.pos,
            current_char: self.current_char,
            current_line: self.current_line,
            is_first: self.is_first,
        }
    }
}

impl Iterator for StreamedLexer {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token()? {
            Err(e) => Some(Err(e)),
            Ok(tk) => Some(Ok(tk)),
        }
    }
}

impl WithState for StreamedLexer {
    type ToState = LexerState;

    fn from_state(state: Self::ToState) -> Self {
        Self::new(CharReader::from_state(state.reader_state))
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        self.reader.pos = state.reader_state.pos;

        self.pos = state.pos;
        self.current_char = state.current_char;
        self.current_line = state.current_line;
        self.is_first = state.is_first;
    }

    fn state(&self) -> Self::ToState {
        Self::ToState::new(
            self.reader.state(),
            self.pos,
            self.current_char,
            self.current_line,
            self.is_first,
        )
    }
}

impl StreamedLexer {
    pub fn new(reader: CharReader) -> StreamedLexer {
        let file = reader.reader.path().to_path_buf();

        Self {
            reader,
            file,
            pos: 0,
            current_char: 1,
            current_line: 1,
            is_first: true,
        }
    }

    /// This is essentially equivalent to next_token, but it resets the lexer back to its previous state.
    /// This means that if you call this two or more times in a row, you will get the same output.
    pub fn peek_next_token(&mut self) -> Option<Result<Token, LexError>> {
        let prev_state = self.state();
        let res = self.next_token();
        self.reset_to_state(prev_state);

        res
    }

    /// This gets the next token from the given CharReader
    /// This will return None when EOF is encountered.
    pub fn next_token(&mut self) -> Option<Result<Token, LexError>> {
        let mut buffer = RefCell::new(String::new());

        let reader = RefCell::from(&mut self.reader);
        let linec = Cell::from_mut(&mut self.current_line);
        let columnc = Cell::from_mut(&mut self.current_char);

        let next_char = |inc: bool| -> Option<char> {
            if inc {
                columnc.set(columnc.get() + 1);
            }

            (*reader.borrow_mut()).next_char()
        };

        let peek_char = || -> Option<char> { reader.borrow().peek_next_char() };

        let Some(c) = next_char(!self.is_first) else {
            // encountered EOF
            return None;
        };

        self.is_first = false;

        match c {
            c if VALID_CHARS.contains(&c) => Some(Ok(Token::Char(
                c,
                LineInfo::new_one_char(columnc.get(), linec.get()),
            ))),

            '#' => loop {
                let Some(next_c) = next_char(true) else {
                    // Encountered EOF
                    return None;
                };

                if next_c == '\n' {
                    linec.set(linec.get() + 1);

                    // comments and whitespace are auto-ignored
                    return self.next_token();
                }
            },

            '\n' => {
                if let None = linec.get().checked_add(1) {
                    return Some(Err(CompilationError::TooManyLines(self.file.clone())));
                } else {
                    linec.set(linec.get() + 1);
                }

                columnc.set(1);

                self.is_first = true;

                self.next_token()
            }

            '\t' => {
                columnc.set(columnc.get() + TAB_SPACES_COUNT as usize);

                self.next_token()
            }

            '"' => {
                let beginc = columnc.get() - 1;
                let beginl = linec.get();

                loop {
                    let Some(next_c) = next_char(true) else {
                        return Some(Err(CompilationError::UnfinishedString(
                            self.file.clone(),
                            LineInfo::new_one_char(beginc, beginl),
                        )));
                    };

                    if next_c == '"' {
                        break;
                    }

                    *buffer.get_mut() += next_c.to_string().as_str();
                }

                let string = buffer.get_mut().to_owned();

                buffer.get_mut().clear();

                let endc = columnc.get();
                let endl = linec.get();

                Some(Ok(Token::String(
                    string,
                    LineInfo::new(beginc.into(), endc, beginl.into(), endl),
                )))
            }

            '\'' => {
                let beginc = columnc.get();
                let beginl = linec.get();

                let Some(c) = next_char(true) else {
                    return Some(Err(CompilationError::UnexpectedEOF(
                        self.file.clone(),
                        "CHAR_LIT".into(),
                    )));
                };

                let linfo = LineInfo::new_one_char(beginc, beginl);

                let Some(peeked) = peek_char() else {
                    return Some(Err(CompilationError::UnfinishedString(
                        self.file.clone(),
                        linfo,
                    )));
                };

                if peeked != '\'' {
                    return Some(Err(CompilationError::InvalidChar(
                        self.file.clone(),
                        peeked,
                        linfo,
                    )));
                }

                next_char(true);

                Some(Ok(Token::Byte(c as u8, linfo)))
            }

            _ => {
                if c.is_whitespace() {
                    //columnc.set(columnc.get() + 1);

                    self.next_token()
                } else if is_mosaic_ident_start(&c) {
                    let beginc = columnc.get();
                    let beginl = linec.get();

                    *buffer.get_mut() += c.to_string().as_str();

                    loop {
                        let Some(next_c) = peek_char() else {
                            break;
                        };

                        if !is_mosaic_ident_part(&next_c) {
                            break;
                        }

                        *buffer.get_mut() += next_c.to_string().as_str();

                        next_char(true);
                    }

                    let ident = buffer.get_mut().to_owned();

                    buffer.get_mut().clear();

                    let endc = columnc.get();

                    Some(Ok(Token::Ident(
                        ident,
                        LineInfo::new(beginc, endc + 1, beginl, beginl),
                    )))
                } else if c.is_numeric() {
                    let beginc = columnc.get();
                    let beginl = linec.get();
                    let mut is_float = false;

                    *buffer.get_mut() += c.to_string().as_str();

                    loop {
                        let Some(next_c) = peek_char() else {
                            break;
                        };

                        // break if character is not numeric, and we have already parsed a floating point number.
                        if !next_c.is_numeric()
                            && ((!next_c.is_numeric() || is_float) && next_c != '.')
                        {
                            break;
                        }

                        if next_c == '.' {
                            is_float = true;
                        }

                        *buffer.get_mut() += next_c.to_string().as_str();

                        next_char(true);
                    }

                    let string = buffer.get_mut().to_owned();
                    let Ok(num) = f64::from_str(string.as_str()) else {
                        unreachable!()
                    };

                    buffer.get_mut().clear();

                    let endc = columnc.get();
                    let endl = linec.get();

                    Some(Ok(Token::Number(
                        num,
                        LineInfo::new(beginc, endc, beginl, endl),
                    )))
                } else {
                    Some(Err(CompilationError::InvalidChar(
                        self.file.clone(),
                        c,
                        LineInfo::new_one_char(columnc.get(), linec.get()),
                    )))
                }
            }
        }
    }
}
