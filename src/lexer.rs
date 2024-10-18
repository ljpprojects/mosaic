use crate::reader::CharReader;
use crate::tokens::{LineInfo, Token};
use std::cell::{Cell, UnsafeCell};
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::num::NonZeroUsize;
use std::os::unix::fs::FileExt;
use std::rc::Rc;
use std::str::FromStr;
use crate::{ptr_op_const, ptr_op_mut};

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

#[derive(Debug)]
pub enum LexError {
    InvalidChar(char, LineInfo),
    UnexpectedEOF,
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

            LexError::UnexpectedEOF => write!(f, "LexError: Unexpected EOF"),
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
pub struct StreamedLexer<R>
where R: FileExt {
    pub(crate) reader: *mut CharReader<R>,
    pos: u64,
    current_char: usize,
    current_line: usize,
    is_first: bool
}

impl<R: FileExt> Clone for StreamedLexer<R> {
    fn clone(&self) -> Self {
        StreamedLexer {
            reader: self.reader,
            pos: self.pos,
            current_char: self.current_char,
            current_line: self.current_line,
            is_first: self.is_first,
        }
    }
}

impl<R: FileExt> Iterator for StreamedLexer<R> {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token()? {
            Err(e) => Some(Err(e)),
            Ok(tk) => Some(Ok(tk)),
        }
    }
}

impl<R: FileExt> StreamedLexer<R> {
    pub fn new(reader: *mut CharReader<R>) -> StreamedLexer<R> {
        Self {
            reader,
            pos: 0,
            current_char: 1,
            current_line: 1,
            is_first: true
        }
    }

    /// This is essentially equivalent to next_token, but it resets the lexer back to its previous state.
    /// This means that if you call this two or more times in a row, you will get the same output.
    pub fn peek_next_token(&mut self) -> Option<Result<Token, LexError>> {
        let prev_pos = unsafe { self.reader.as_ref().unwrap() }.pos;
        let prev_line = self.current_line;
        let prev_column = self.current_char;
        let was_first = self.is_first;

        let res = self.next_token();

        unsafe { (*self.reader).pos = prev_pos }

        self.current_char = prev_column;
        self.current_line = prev_line;
        self.is_first = was_first;

        res
    }

    /// This gets the next token from the given CharReader
    /// This will return None when EOF is encountered.
    pub fn next_token(&mut self) -> Option<Result<Token, LexError>> {
        let buffer = UnsafeCell::new(String::new());

        let stream = self.reader;

        let linec: *mut usize = &mut self.current_line;
        let columnc: *mut usize = &mut self.current_char;

        let mut next_char = |inc: bool| -> Option<char> {
            if inc {
                unsafe {
                    *columnc += 1;
                }
            }

            ptr_op_mut! {
                stream => next_char
            }
        };

        let mut peek_char = || -> Option<char> {
            ptr_op_mut! {
                stream => peek_next_char
            }
        };

        let Some(c) = next_char(!self.is_first) else {
            // encountered EOF
            return None
        };

        self.is_first = false;

        match c {
            '+' | '-' | '*' | '/' | '%' | ':' | '^' | '?' | '!' | '=' | '>' | '<' | '{' | '}'
            | '[' | ']' | '(' | ')' | '@' | ',' | '&' | '|' | '.' => {
                Some(Ok(Token::Char(
                    c,
                    LineInfo::new_one_char(
                        Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap()),
                        Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap())
                    ),
                )))
            }

            '#' => loop {
                let Some(next_c) = next_char(true) else {
                    // Encountered EOF
                    return None
                };

                if next_c == '\n' {
                    unsafe { *linec += 1 }

                    // comments and whitespace are auto-ignored
                    return self.next_token()
                }
            },

            '\n' => {
                if let None = unsafe { *linec }.checked_add(1) {
                    return Some(Err(LexError::TooManyLines));
                } else {
                    unsafe { *linec += 1 }
                }

                unsafe { *columnc = 1 }

                self.is_first = true;

                self.next_token()
            }

            '\t' => {
                unsafe { *columnc += TAB_SPACES_COUNT as usize }

                self.next_token()
            }

            '"' => {
                let beginc = Rc::from(NonZeroUsize::new(unsafe { *columnc } - 1).unwrap());
                let beginl = Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap());

                loop {
                    let Some(next_c) = next_char(true) else {
                        return Some(Err(LexError::UnfinishedString(LineInfo::new_one_char(
                            beginc,
                            beginl
                        ))));
                    };

                    if next_c == '"' {
                        break;
                    }

                    unsafe { *buffer.get() += next_c.to_string().as_str() }
                }

                let string = ptr_op_const! {
                    buffer.get() => to_owned
                };

                ptr_op_mut! {
                    buffer.get() => clear
                }

                let endc = Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap());
                let endl = Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap());

                Some(Ok(Token::String(
                    string,
                    LineInfo::new(beginc, endc, beginl, endl),
                )))
            }

            _ => {
                if c.is_whitespace() {
                    unsafe { *columnc += 1 }

                    return self.next_token()
                } else if is_mosaic_ident_start(&c) {
                    let beginc = Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap());
                    let beginl = Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap());

                    unsafe { *buffer.get() += c.to_string().as_str() }

                    loop {
                        let Some(next_c) = peek_char() else {
                            break;
                        };

                        if !is_mosaic_ident_part(&next_c) {
                            break;
                        }

                        unsafe { *buffer.get() += next_c.to_string().as_str() }

                        next_char(true);
                    }

                    let ident = ptr_op_const! {
                        buffer.get() => to_owned
                    };

                    ptr_op_mut! {
                        buffer.get() => clear
                    }

                    let endc = Rc::from(beginc.checked_add(ident.len()).unwrap());

                    println!("{}", ident.len());

                    return Some(Ok(Token::Ident(
                        ident,
                        LineInfo::new(beginc, endc, beginl.clone(), beginl),
                    )))
                } else if c.is_numeric() {
                    let beginc = Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap());
                    let beginl = Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap());
                    let mut is_float = false;

                    unsafe { *buffer.get() += c.to_string().as_str() }

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

                        unsafe { *buffer.get() += next_c.to_string().as_str() };

                        next_char(true);
                    }

                    let string = unsafe { buffer.get().as_ref().unwrap() };
                    let num = f64::from_str(string.as_str()).unwrap();

                    ptr_op_mut! {
                        buffer.get() => clear
                    }

                    let endc = Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap());
                    let endl = Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap());

                    return Some(Ok(Token::Number(
                        num,
                        LineInfo::new(beginc, endc, beginl, endl),
                    )))
                }

                Some(Err(LexError::InvalidChar(
                    c,
                    LineInfo::new_one_char(Rc::from(NonZeroUsize::new(unsafe { *columnc }).unwrap()), Rc::from(NonZeroUsize::new(unsafe { *linec }).unwrap())),
                )))
            }
        }
    }
}