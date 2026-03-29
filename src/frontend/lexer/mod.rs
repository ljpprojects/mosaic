pub mod debug;
pub mod errors;
pub mod tokens;

use crate::frontend::lexer::debug::{PositionRange, TokenContext};
use crate::frontend::lexer::errors::LexError;
use crate::reader::CharReader;
use crate::states::{LexerState, Position, WithState};
use crate::frontend::lexer::tokens::Token;
use std::cell::{Cell, RefCell};
use std::num::{NonZeroU8, NonZeroU16};
use std::str::FromStr;

/// A sorted list of legal characters. They are categorised like this:
///
/// Punctuation:  ';', '?', '!', '.', ',';
///
/// Mathematical: '<', '>', '=', '-', '+', '*';
///
/// Grouping:     '(', ')', '[', ']', '{', '}';
///
/// Miscellaneous '#', '&', '$', '@', ':', '|',
///               '`', '~', '^', '"', '\'', '\\'
pub const LEGAL_CHARS: &[char] = &[
    '!', '"', '#', '$', '&',
    '\'', '(', ')', '*', '+',
    ',', '-', '.', ':', ';',
    '<', '=', '>', '?', '@',
    '[', '\\', ']', '^', '`',
    '{', '|', '}', '~',
];

/// A sorted list of keywords. They are categorised like this:
///
/// Definitions:   fn, interface, impl, synthesise, alias
///                let, mut, enum, extern, default;
///
/// Control Flow:  return, if, else, match, switch, for,
///                while, do, break, goto, continue, in;
///
/// MSR:           region, escape;
///
/// Miscellaneous: unsafe, as, true, false, alignof, into
///                sizeof, include;
pub const KEYWORDS: &[&str] = &[
    "alias", "alignof", "as", "break", "bytes", "comment", "continue",
    "default", "do", "else", "enum", "escape", "extern", "false", "fn", "for",
    "goto", "guard", "if", "impl", "in", "include", "interface", "into", "let",
    "match", "mut", "namespace", "propagate", "region", "return", "section",
    "sizeof", "stackalloc", "string", "switch", "synthesise", "true", "unsafe",
    "while", "zam", "zamalamadingdong", "zzz",
];

/// A sorted list of keywords. They are categorised like this:
///
/// Synthesis:     @strong, @weak, @assign, @copy, @take;
///
/// Linkage:       @export, @nomangle, @local, @hidden;
///
/// Visibility:    @private, @protected, @public, @fileprivate;
///
/// Usage:         @required, @readonly, @deprecated, @unsafe, @unused, @final;
///
/// Optimisations: @const;
pub const MODIFIERS: &[&str] = &[
    "allocates", "assign", "const", "copy", "deprecated", "export",
    "fileprivate", "final", "hidden", "inline", "layout", "local", "nomangle",
    "private", "protected", "public", "readonly", "return", "required", "take",
    "unsafe", "unused",
];

pub fn is_mosaic_ident_start(c: &char) -> bool {
    c.is_alphabetic()
}

pub fn is_mosaic_ident_part(c: &char) -> bool {
    c.is_alphanumeric()
}

/// This is the lexer for the Mosaic programming language.
/// Like the CharReader struct, it returns tokens individually, allowing for better performance (?),
/// especially for large files (this claim is unproven as of 20/03/2026).
#[derive(Debug, PartialEq, Clone)]
pub struct StreamedLexer<'a> {
    pub(crate) reader: CharReader<'a>,
    pos: Position,
    cur_context: Option<TokenContext>,
}

impl Iterator for StreamedLexer<'_> {
    type Item = Result<(Token, PositionRange), LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token()? {
            Err(e) => Some(Err(e)),
            Ok(tk) => Some(Ok(tk)),
        }
    }
}

impl<'a> WithState for StreamedLexer<'a> {
    type ToState = LexerState<'a>;

    fn from_state(state: Self::ToState) -> Self {
        Self::new(CharReader::from_state(state.reader_state))
    }

    fn reset_to_state(&mut self, state: Self::ToState) {
        self.reader.reset_to_state(state.reader_state);
        self.pos = state.pos;
        self.cur_context = state.cur_context;
    }

    fn state(&self) -> Self::ToState {
        Self::ToState::new(
            self.reader.state(),
            self.pos,
            self.cur_context,
        )
    }
}

impl<'a> StreamedLexer<'a> {
    pub fn new(reader: CharReader<'a>) -> StreamedLexer {
        Self {
            reader,
            pos: Position {
                offset: 0,
                // 1 != 0
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            cur_context: None,
        }
    }

    /// This is essentially equivalent to next_token, but it resets the lexer back to its previous state.
    /// This means that if you call this two or more times in a row, you will get the same output.
    pub fn peek_next_token(&mut self) -> Option<Result<(Token, PositionRange), LexError>> {
        let prev_state = self.state();
        let res = self.next_token();
        self.reset_to_state(prev_state);

        res
    }

    pub fn next_char(&mut self, ignore_whitespace: bool) -> Option<Result<char, LexError>> {
        let next = self.reader.next_char()?;

        if let Some(nc) = self.pos.column.checked_add(1) {
            self.pos.column = nc;
        } else {
            return Some(Err(LexError::TooManyColumns(self.cur_context, self.pos.line)))
        }

        // Check for newline if we are skipping whitespace
        if (next == '\n' || next == '\r') && !ignore_whitespace {
            if let Some(nl) = self.pos.line.checked_add(1) {
                self.pos.line = nl;
            } else {
                return Some(Err(LexError::TooManyLines(self.cur_context)))
            }

            self.pos.column = unsafe { NonZeroU8::new_unchecked(1) };
            self.pos.offset += 1;

            return self.next_char(false);
        }

        // Check for whitespace
        if next.is_whitespace() && !ignore_whitespace {
            self.pos.offset += 1;
            return self.next_char(false)
        }

        self.pos.offset += 1;
        Some(Ok(next))
    }

    pub fn prev_char(&mut self, ignore_whitespace: bool) -> Option<char> {
        let prev = self.reader.prev_char()?;

        if self.pos.offset == 0 {
            // At the start of the file, there is no previous character
            return None
        }

        // Why don't NonZero types have checked_sub or something??????
        if let Some(nc) = NonZeroU8::new(self.pos.column.get() - 1) {
            self.pos.column = nc;
        } else {
            // We are at the start of the line, if line is 1 then we should
            // return None, otherwise prev MUST be a newline and we need to go
            // back a line goto would be peak

            if self.pos.line.get() == 1 {
                return None
            }

            if let Some(nl) = NonZeroU16::new(self.pos.line.get() - 1) && !ignore_whitespace {
                self.pos.line = nl;
            } else {
                // This case has been handled already (offset is 0 if we are
                // here) but for clarity put it here again
                return None;
            }
        }

        // No need to check for newlines as the else case of the last if-let
        // handled that already

        // Check for whitespace
        if next.is_whitespace() && !ignore_whitespace {
            self.pos.offset -= 1;
            return self.prev_char(false)
        }

        self.pos.offset -= 1;
        Some(next)
    }

    /// ## Invariants
    /// - The preceeding # has been consumed already
    ///
    /// ## Returns
    /// The comment's contents (excluding delimiters) and its PositionRange, and
    /// the next token and its PositionRange
    pub fn lex_comment(&mut self) ->  Result<((String, PositionRange), Option<(Token, PositionRange)>), LexError> {
        let prev_context = self.cur_context;
        self.cur_context = Some(TokenContext::Comment);

        let Some(upcoming) = self.reader.peek_next_char() else {
            self.cur_context = prev_context;
            return Ok(((
                String::default(),
                PositionRange::one_char(
                    self.reader.path.into(),
                    self.pos,
                    self.cur_context
                )
            ), None));
        };

        let mut comment_contents = String::new();

        let start_pos = self.pos.clone();

        // # is a line comment, #/ is a block comment
        match upcoming {
            '\n' => (),
            '/' => {
                let mut partial_br_flag = false;

                loop {
                    let Some(next) = self.next_char(true).transpose()? else {
                        self.cur_context = prev_context;
                        return Ok(((
                            comment_contents,
                            PositionRange::new(
                                self.reader.path.into(),
                                start_pos,
                                self.pos,
                                self.cur_context
                            )
                        ), None));
                    };

                    if next == '/' && !partial_br_flag {
                        partial_br_flag = true;
                        continue;
                    }

                    if next == '#' && partial_br_flag {
                        break;
                    }

                    comment_contents.push(next);
                }
            },
            _ => loop {
                let Some(next) = self.next_char(true).transpose()? else {
                    self.cur_context = prev_context;
                    return Ok(((
                        comment_contents,
                        PositionRange::new(
                            self.reader.path.into(),
                            start_pos,
                            self.pos,
                            self.cur_context
                        )
                    ), None));
                };

                if next == '\n' {
                    break;
                }

                comment_contents.push(next);
            }
        }

        self.cur_context = prev_context;

        return Ok(((
            comment_contents,
            PositionRange::new(
                self.reader.path.into(),
                start_pos,
                self.pos,
                self.cur_context
            )
        ), self.next_token().transpose()?));
    }

    /// Parsers a modifier, assuming the preceeding '@' has already been consumed.
    /// If an error is returned, no state is changed
    pub fn lex_modifier(&mut self) -> Result<(Token, PositionRange), LexError> {
        let begin_state = self.state();
        let mut buf = String::new();

        self.cur_context = Some(TokenContext::Modifier);

        loop {
            let Some(next) = self.next_char(true).transpose()? else {
                if let Ok(idx) = MODIFIERS.binary_search(&&*buf) {
                    return Ok((
                        Token::Modifier(MODIFIERS[idx]),
                        PositionRange::new(
                            self.reader.path.into(),
                            begin_state.pos,
                            self.pos,
                            self.cur_context
                        )
                    ))
                }

                let err = Err(LexError::UnexpectedEOF(self.cur_context));
                self.reset_to_state(begin_state);

                return err
            };

            if !next.is_ascii_alphabetic() {
                self.prev_char(true);
                break;
            }

            buf.push(next);
        }

        // Modifiers are case-insensitive
        buf.make_ascii_lowercase();

        if let Ok(idx) = MODIFIERS.binary_search(&&*buf) {
            Ok((
                Token::Modifier(MODIFIERS[idx]),
                PositionRange::new(
                    self.reader.path.into(),
                    begin_state.pos,
                    self.pos,
                    self.cur_context
                )
            ))
        } else {
            let err = Err(LexError::UnexpectedEOF(self.cur_context));
            self.reset_to_state(begin_state);

            return err
        }
    }

    /// This gets the next token from the given CharReader
    /// This will return None when EOF is encountered.
    pub fn next_token(&mut self) -> Option<Result<(Token, PositionRange), LexError>> {
        let c = match self.next_char(false)? {
            Ok(c) => c,
            Err(e) => return Some(Err(e))
        };

        let res = match c {
            '#' => self.lex_comment().map(|r| r.1).transpose(),
            '"' => self.lex_string(),
            '\'' => self.lex_char_lit(),
            '@' => Some(self.lex_modifier()),
            c if c.is_ascii_alphabetic() => self.lex_alphabetical(),
            c if is_mosaic_ident_start(&c) => self.lex_ident(),
            c if c.is_ascii_digit() => self.lex_number(),
            c if LEGAL_CHARS.binary_search(&c).is_ok() =>
                Some(Ok(
                    (
                        Token::Symbol(c),
                        PositionRange::one_char(
                            self.reader.path.into(),
                            self.pos,
                            self.cur_context
                        )
                    )
                )),
            _ => todo!(),
        };

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
