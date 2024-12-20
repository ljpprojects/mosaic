#![forbid(unsafe_code)]

use crate::reader::CharReader;
use crate::states::{LexerState, WithState};
use crate::tokens::{LineInfo, Token};
use std::cell::{Cell, RefCell};
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::str::FromStr;

/// This is equal to amount spaces a tab character is equal to.
/// This is important because without it the character position system does not work.
/// Can be overridden via the config key 'formatting.tab_space_count', or the '--tab-space-count' option.
///
/// `mosaic run file.mosaic --tab-space-count 2`
/// or
///
/// **config.mosaic.toml**
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

#[derive(Debug, Clone)]
pub enum LexError {
    InvalidChar(char, LineInfo),
    UnfinishedString(LineInfo),
    TooManyLines,
}

impl Display for LexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LexError::InvalidChar(c, line_info) => {
                write!(f, "LexError: Invalid character {c} at {line_info}")
            }

            LexError::UnfinishedString(line_info) => {
                write!(f, "LexError: Unfinished string at {line_info}")
            }

            LexError::TooManyLines => write!(f, "LexError: Too many lines in source file"),
        }
    }
}

// macro example
/*
    ptr_as_mut!(stream)
*/

impl Error for LexError {}

/// This is the lexer for the Mosaic programming language.
/// Like the CharReader struct, it returns tokens individually, allowing for better performance,
/// especially for large files.
#[derive(Debug)]
#[derive(PartialEq)]
pub struct StreamedLexer {
    pub(crate) reader: CharReader,
    pos: u64,
    current_char: usize,
    current_line: usize,
    is_first: bool,
}

impl Clone for StreamedLexer {
    fn clone(&self) -> Self {
        StreamedLexer {
            reader: self.reader.clone(),
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
        Self {
            reader,
            pos: 0,
            current_char: 1,
            current_line: 1,
            is_first: true,
        }
    }

    /// This is essentially equivalent to next_token, but it resets the lexer back to its previous state.
    /// This means that if you call this two or more times in a row, you will get the same output.
    pub fn peek_next_token(&mut self) -> Option<Result<Token, LexError>> {
        /*let prev_pos = self.reader.pos;
        let prev_line = self.current_line;
        let prev_column = self.current_char;
        let was_first = self.is_first;*/

        let prev_state = self.state();

        let res = self.next_token();

        /*self.reader.pos = prev_pos;
        self.current_char = prev_column;
        self.current_line = prev_line;
        self.is_first = was_first;*/

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
            '+' | '-' | '*' | '/' | '%' | ':' | '^' | '?' | '!' | '=' | '>' | '<' | '{' | '}'
            | '[' | ']' | '(' | ')' | '@' | ',' | '&' | '|' | '.' => Some(Ok(Token::Char(
                c,
                LineInfo::new_one_char(
                    Rc::from(NonZeroUsize::new(columnc.get()).unwrap()),
                    Rc::from(NonZeroUsize::new(columnc.get()).unwrap()),
                ),
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
                    return Some(Err(LexError::TooManyLines));
                } else {
                    linec.set(linec.get() + 1);
                }

                columnc.set(columnc.get() + 1);

                self.is_first = true;

                self.next_token()
            }

            '\t' => {
                columnc.set(columnc.get() + TAB_SPACES_COUNT as usize);

                self.next_token()
            }

            '"' => {
                let beginc = Rc::from(NonZeroUsize::new(columnc.get() - 1).unwrap());
                let beginl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());

                loop {
                    let Some(next_c) = next_char(true) else {
                        return Some(Err(LexError::UnfinishedString(LineInfo::new_one_char(
                            beginc, beginl,
                        ))));
                    };

                    if next_c == '"' {
                        break;
                    }

                    *buffer.get_mut() += next_c.to_string().as_str();
                }

                let string = buffer.get_mut().to_owned();

                buffer.get_mut().clear();

                let endc = Rc::from(NonZeroUsize::new(columnc.get()).unwrap());
                let endl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());

                Some(Ok(Token::String(
                    string,
                    LineInfo::new(beginc, endc, beginl, endl),
                )))
            }
            
            '\'' => {
                let beginc = Rc::from(NonZeroUsize::new(columnc.get()).unwrap());
                let beginl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());
                
                let c = next_char(true).unwrap() as u8;
                
                let linfo = LineInfo::new_one_char(beginc, beginl);
                
                if peek_char().unwrap() != '\'' {
                    return Some(Err(LexError::InvalidChar(peek_char().unwrap(), linfo)));
                }
                
                next_char(true);

                Some(Ok(Token::Byte(c, linfo)))
            }

            _ => {
                if c.is_whitespace() {
                    columnc.set(columnc.get() + 1);

                    return self.next_token();
                } else if is_mosaic_ident_start(&c) {
                    let beginc = Rc::from(NonZeroUsize::new(columnc.get()).unwrap());
                    let beginl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());

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

                    let endc = Rc::from(beginc.checked_add(ident.len()).unwrap());

                    return Some(Ok(Token::Ident(
                        ident,
                        LineInfo::new(beginc, endc, beginl.clone(), beginl),
                    )));
                } else if c.is_numeric() {
                    let beginc = Rc::from(NonZeroUsize::new(columnc.get()).unwrap());
                    let beginl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());
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
                    let num = f64::from_str(string.as_str()).unwrap();

                    buffer.get_mut().clear();

                    let endc = Rc::from(NonZeroUsize::new(columnc.get()).unwrap());
                    let endl = Rc::from(NonZeroUsize::new(linec.get()).unwrap());

                    return Some(Ok(Token::Number(
                        num,
                        LineInfo::new(beginc, endc, beginl, endl),
                    )));
                }

                Some(Err(LexError::InvalidChar(
                    c,
                    LineInfo::new_one_char(
                        Rc::from(NonZeroUsize::new(columnc.get()).unwrap()),
                        Rc::from(NonZeroUsize::new(linec.get()).unwrap()),
                    ),
                )))
            }
        }
    }
}
