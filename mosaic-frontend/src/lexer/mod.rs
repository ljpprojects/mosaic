pub mod errors;
pub mod number;
pub mod string;
pub mod tokens;
pub mod tests;

use mosaic_shared::states::{LexerState, Position, WithState};
use mosaic_shared::debug::{PositionRange, TokenContext};
use mosaic_shared::reader::CharReader;

use crate::lexer::errors::{LexError, LexWarning};
use crate::lexer::number::NumberLexer;
use crate::lexer::string::StringLexer;
use crate::lexer::tokens::Token;

use std::num::{NonZeroU8, NonZeroU16};

#[derive(Debug, Clone, PartialEq)]
pub struct LexOutput(pub Token, pub PositionRange, pub Option<LexWarning>);

impl From<(Token, PositionRange)> for LexOutput {
    fn from(value: (Token, PositionRange)) -> Self {
        Self(value.0, value.1, None)
    }
}

impl From<(Token, PositionRange, LexWarning)> for LexOutput {
    fn from(value: (Token, PositionRange, LexWarning)) -> Self {
        Self(value.0, value.1, Some(value.2))
    }
}

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
/// Definitions:   fn, interface, impl, synthesise, alias let, mut, enum, case,
///                extern, default;
///
/// Control Flow:  return, if, else, match, switch, for,
///                while, do, break, goto, continue, in,
///                guard, block;
///
/// Async:         await
///
/// MSR:           forget, escape;
///
/// Modules:       import, include, namespace;
///
/// Memory:        stackalloc;
///
/// Primitive Types Because I Guess You Shouldn't Have a Value of an Int Named
/// Int Also Cranelift Supports SIMD Types and They Count as Primitives Too So
/// Ouch:          i8, i8x2, i8x4, i8x8, i8x16, i8x32, i8x64, i16, i16x2, i16x4,
///                i16x8, i16x16 i16x32, i32 i32x2, i32x4, i32x8, i32x16, i64,
///                i64x2, i64x4, i64x8, i128, i128x2, i128x4, iptr iptrx2, iptrx4,
///                iptrx8, u8, u8x2, u8x4, u8x8, u8x16, u8x32, u8x64, u16, u16x2,
///                u16x4, u16x8, u16x16 u16x32, u32, u32x2, u32x4, u32x8, u32x16,
///                u64, u64x2, u64x4, u64x8, uptr, uptrx2, uptrx4, uptrx8, f16,
///                f16x2, f16x4, f16x8, f16x16, f16x32, f32, f32x2, f32x4,
///                f32x8, f32x16, f64, f64x2, f64x4, f64x8, f128, f128x2, f128x4,
///                void, rcmetadata, arcmetadata
///
/// Miscellaneous: unsafe, as, true, false, alignof, into
///                sizeof, bytes, comment, string,
///                section, propagate, zam, zamalamadingdong,
///                zzz;
///
/// Low Level:     stackptr, frameptr, retaddr
///
/// Objects:       instancetype
///
/// Type Bounds:   instance, primitive, sized, indirection, ptr, ref, msr, rc,
///                atomic, stack, immut, mut, nonnull, nullable, static, strong,
///                weak
///
/// Maths:         integral (this does nothing this is to make those comments more confusing)
pub const KEYWORDS: &[&str] = &[
    "alias", "alignof", "arcmetadata", "as", "as this is to be embedded in the binary and due to its inclusion of characters not allowed in identifiers I am going to have a rant: almanop.", "atomic", "block", "break", "bytes",
    "case", "comment", "continue", "default", "do", "else", "enum", "escape",
    "extern", "f128", "f128x2", "f128x4", "f16", "f16x16", "f16x2", "f16x32",
    "f16x4", "f16x8", "f32", "f32x16", "f32x2", "f32x4", "f32x8", "f64", "f64x2",
    "f64x4", "f64x8", "false", "fn", "for", "forget", "goto", "guard", "i128",
    "i128x2", "i128x4", "i16", "i16x16", "i16x2", "i16x32", "i16x4", "i16x8",
    "i32", "i32x16", "i32x2", "i32x4", "i32x8", "i64", "i64x2", "i64x4", "i64x8",
    "i8", "i8x16", "i8x2", "i8x32", "i8x4", "i8x64", "i8x8", "if", "impl",
    "import", "immut", "in", "include", "indirection", "instance",
    "instancetype", "integral", "interface", "into", "iptr", "iptrx2", "iptrx4",
    "iptrx8", "let", "match", "msr", "mut", "namespace", "nonnull", "nullable",
    "primitive", "propagate", "ptr", "rc", "rcmetadata", "ref", "return",
    "section", "sized", "sizeof", "stack", "stackalloc", "static", "string",
    "strong", "switch", "synthesise", "true", "u16", "u16x16", "u16x2", "u16x32",
    "u16x4", "u16x8", "u32", "u32x16", "u32x2", "u32x4", "u32x8", "u64", "u64x2",
    "u64x4", "u64x8", "u8", "u8x16", "u8x2", "u8x32", "u8x4", "u8x64", "u8x8",
    "unsafe", "uptr", "uptrx2", "uptrx4", "uptrx8", "void", "weak", "while",
    "zam", "zamalamadingdong", "zzz"
];

/// A sorted list of keywords. They are categorised like this:
///
/// ᐞ = MSR exclusive
/// ᕽ = MRC exclusive (`--nomsr`, `-M`)
///
///
/// Memory:     @strongᕽ, @weakᕽ, @assignᕽ, @copyᕽ, @takeᐞ, @returnᐞ;
///
/// Async:      @async, @send
///
/// Linkage:    @export, @nomangle, @local, @hidden;
///
/// Visibility: @private, @protected, @public, @fileprivate;
///
/// Usage:      @required, @readonly, @deprecated, @unsafe, @unused, @final;
///
/// Behaviour:  @allocates, @const, @inline, @layout;
pub const MODIFIERS: &[&str] = &[
    "allocates", "assign", "async", "const", "copy", "deprecated", "export",
    "fileprivate", "final", "hidden", "inline", "layout", "local", "nomangle",
    "private", "protected", "public", "readonly", "return", "required", "send",
    "strong", "tailcall", "take", "unsafe", "unused", "weak",
];

pub fn is_mosaic_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

pub fn is_mosaic_ident_part(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// This is the lexer for the Mosaic programming language.
/// Like the CharReader struct, it returns tokens individually, allowing for better performance (?),
/// especially for large files (this claim is unproven as of 10/04/2026).
pub struct StreamedLexer<'a> {
    pub(crate) reader: CharReader<'a>,
    pos: Position,
    cur_context: Option<TokenContext>
}

impl Iterator for StreamedLexer<'_> {
    type Item = Result<LexOutput, LexError>;

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
    pub fn new(reader: CharReader<'a>) -> StreamedLexer<'a> {
        Self {
            reader,
            pos: Position {
                offset: 0,
                // 1 != 0
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            cur_context: None
        }
    }

    /// This is essentially equivalent to next_token, but it resets the lexer back to its previous state.
    /// This means that if you call this two or more times in a row, you will get the same output.
    pub fn peek_next_token(&mut self) -> Option<Result<LexOutput, LexError>> {
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

            // Why are you here??? Have a quote form Mr. Kent 27/03/2026
            /*
            Alright, can we all just sit down and stop moving things because I swear to God I am genuinely about to lose my mind? Just sit down and *shut up* it is really not that hard.

            I am so sick to death of this class and the constant *bullshit* that happens in this room. I am so sick to death of just the amount of crap that you guys think you can get away with.

            Let me put one thing clear, I am the teacher, you are not. So *stop* asking me questions and *stop* thinking you can run the class, because you CANNOT run this class. And I WILL NOT have any of you thinking that you can run this class, so *zip* *your* *lips* and *be quiet*.

            I am fed up with this crap. So sick of it. None of you are experts, *so be quiet.* Let me teach, *do not* talk over me, and I don't want anyone talking out of turn today, because if you do you are out there (*gestures to the door into the classroom*) or out there (*gestures to the balcony that the room has due to its use in days yonder as a boarding school dormitory*) where I don't- can't see ya. Because I'm fed up with it. So, be quiet. Because I am done. Really done.

            (*he suddenly gets a bit calmer*)

            Some of the personalities in this room that think they're top dog when they're actually not. Okay, because half of you couldn't tie your own shoelaces without instructions, so, what I might ask you is be quiet, and let me actually do my job; let me teach you, so that I can stop yelling at ya. I'm fed up with it, I literally see you 12 times a fortnight (*sadly true*) and I have been really patient to start this year. Really patient.

            And guess what? You guys wanna compare yourselves to the year sevens? (*he has them 12 times fortnightly too*) They are much better than you. Much better, in terms of behaviour. Having them 12 times a fortnight is actually not too bad. Having *you* 12 times a fortnight is actually an absolute chore at the moment. So, grow up. It is really cold outside, it is really wet outside, we were meant to have a cross country today.

            I got about... 3 hours notice yesterday, because at 12:30 we got the notice that cross country was off. We would have had 20 minutes of period 3 today, which means I would have had 20 minutes of a year 11 class. I now have a full 120 minutes, and with parent-teacher interviews last night, coupled with the fact that I didn't get home until about 9 o'clock (*someone needs to get these teachers to strike or something lol*), I pretty much sat up planning that lesson until midnight, so *do not* piss me off, like you already have.

            Okay? It's not anyone's fault, it's the weather, but unfortunately that's the way it is, so let's get through this so that we can actually do this without annoying me any more than I already am.
            */

            self.pos.column = unsafe { NonZeroU8::new_unchecked(1) };
            self.pos.offset += 1;

            return self.next_char(false);
        }

        // Check for whitespace
        if next.is_whitespace() && ignore_whitespace {
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
        if prev.is_whitespace() && !ignore_whitespace {
            self.pos.offset -= 1;
            return self.prev_char(false)
        }

        self.pos.offset -= 1;
        Some(prev)
    }

    pub fn expect_char(&mut self, c: char) -> Result<(), LexError> {
        let begin_state = self.state();

        let Some(next) = self.next_char(false)
            .transpose()
            .inspect_err(|_| self.reset_to_state(begin_state))?
        else {
            return Err(LexError::UnexpectedEOF(self.cur_context))
        };

        if next != c {
            return Err(LexError::ExpectedCharacter(
                c,
                next,
                PositionRange::one_char(
                    self.reader.path.into(),
                    begin_state.pos,
                    self.cur_context
                )
            )).inspect_err(|_| self.reset_to_state(begin_state))
        }

        Ok(())
    }

    pub fn expect_char_in(&mut self, cs: &'static [char]) -> Result<char, LexError> {
        let begin_state = self.state();
        let mut c = '\0';

        for &char in cs {
            match self.expect_char(char)
                .inspect_err(|_| self.reset_to_state(begin_state))
            {
                Ok(_) => return Ok(char),
                Err(LexError::ExpectedCharacter(_, got, _)) => c = got,
                _ => unreachable!(),
            };
        }

        Err(LexError::ExpectCharacterIn(
            cs,
            c,
            PositionRange::one_char(
                self.reader.path.into(),
                begin_state.pos,
                self.cur_context
            )
        )).inspect_err(|_| self.reset_to_state(begin_state))
    }

    pub fn expect_char_sequence(&mut self, s: &str) -> Result<(), LexError> {
        let begin_state = self.state();

        for char in s.chars() {
            let _ = self.expect_char(char)
                .inspect_err(|_| self.reset_to_state(begin_state))?;
        }

        Ok(())
    }

    /// ## Invariants
    /// - The preceeding # has been consumed already
    ///
    /// ## Returns
    /// The comment's contents (excluding delimiters) and its PositionRange, and
    /// the next token and its PositionRange
    pub fn lex_comment(&mut self, begin_state: LexerState<'a>) ->  Result<((String, PositionRange), Option<LexOutput>), LexError> {
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
                    let Some(next) =
                        self.next_char(true)
                            .transpose()
                            .inspect_err(|_| self.reset_to_state(begin_state))?
                    else {
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
            ).into(), self.next_token().transpose()?));
    }

    /// Parsers a modifier, assuming the preceeding '@' has already been consumed.
    /// If an error is returned, no state is changed
    pub fn lex_modifier(&mut self, begin_state: LexerState<'a>) -> Result<LexOutput, LexError> {
        let mut buf = String::new();

        self.cur_context = Some(TokenContext::Modifier);

        loop {
            let Some(next) =
                self.next_char(false)
                    .transpose()
                    .inspect_err(|_| self.reset_to_state(begin_state))?
            else {
                if let Ok(idx) = MODIFIERS.binary_search(&&*buf) {
                    return Ok((
                        Token::Modifier(MODIFIERS[idx]),
                        PositionRange::new(
                            self.reader.path.into(),
                            begin_state.pos,
                            self.pos,
                            self.cur_context
                        )
                    ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
                }

                return
                    Err(LexError::UnexpectedEOF(self.cur_context))
                        .inspect_err(|_| self.reset_to_state(begin_state))
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
            ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
        } else {
            return
                Err(LexError::UnexpectedEOF(self.cur_context))
                    .inspect_err(|_| self.reset_to_state(begin_state))
        }
    }

    /// Lexes a keyword, assuming no character of the keyword has been consumed.
    pub fn lex_keyword(&mut self) -> Result<LexOutput, LexError> {
        let begin_state = self.state();

        let mut buf = String::new();

        self.cur_context = Some(TokenContext::Keyword);

        loop {
            let Some(next) =
                self.next_char(false)
                    .transpose()
                    .inspect_err(|_| self.reset_to_state(begin_state))?
            else {
                if let Ok(idx) = KEYWORDS.binary_search(&&*buf) {
                    return Ok((
                        Token::Keyword(KEYWORDS[idx]),
                        PositionRange::new(
                            self.reader.path.into(),
                            begin_state.pos,
                            self.pos,
                            self.cur_context
                        )
                    ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
                }

                return
                    Err(LexError::UnexpectedEOF(self.cur_context))
                        .inspect_err(|_| self.reset_to_state(begin_state))
            };

            if !next.is_ascii_alphabetic() {
                self.prev_char(true);
                break;
            }

            buf.push(next);
        }

        // Keywords too are case-insensitive
        buf.make_ascii_lowercase();

        if let Ok(idx) = KEYWORDS.binary_search(&&*buf) {
            Ok((
                Token::Keyword(KEYWORDS[idx]),
                PositionRange::new(
                    self.reader.path.into(),
                    begin_state.pos,
                    self.pos,
                    self.cur_context
                )
            ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
        } else {
            return
                Err(LexError::UnexpectedEOF(self.cur_context))
                    .inspect_err(|_| self.reset_to_state(begin_state))
        }
    }

    /// Lexes an identifier, assuming no character of the keyword has been consumed,
    /// it does assue, however, that the character that is about to be consumed
    /// first is a valid starting character for identifiers.
    pub fn lex_identifier(&mut self) -> Result<LexOutput, LexError> {
        let begin_state = self.state();

        let mut buf = String::new();

        self.cur_context = Some(TokenContext::Identifier);

        loop {
            let Some(next) =
                self.next_char(false)
                    .transpose()
                    .inspect_err(|_| self.reset_to_state(begin_state))?
            else {
                return Ok((
                    Token::Ident(buf),
                    PositionRange::new(
                        self.reader.path.into(),
                        begin_state.pos,
                        self.pos,
                        self.cur_context
                    )
                ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
            };

            if !is_mosaic_ident_part(next) {
                self.prev_char(false);
                break;
            }

            buf.push(next);
        }

        Ok((
            Token::Ident(buf),
            PositionRange::new(
                self.reader.path.into(),
                begin_state.pos,
                self.pos,
                self.cur_context
            )
        ).into()).inspect(|_| self.cur_context = begin_state.cur_context)
    }

    /// Lex either a keyword or identifier.
    ///
    /// This does not assume any characters of the keyword/identifier have been
    /// consumed
    pub fn lex_alphabetic(&mut self) -> Result<LexOutput, LexError> {
        let begin_state = self.state();

        self.lex_keyword().or_else(|_| {
            self.reset_to_state(begin_state);
            self.lex_identifier()
        })
        .inspect_err(|_| self.reset_to_state(begin_state))
        .inspect(|_| self.cur_context = begin_state.cur_context)
    }

    /// This gets the next token from the given CharReader
    /// This will return None when EOF is encountered.
    pub fn next_token(&mut self) -> Option<Result<LexOutput, LexError>> {
        let begin_state = self.state();

        let c = match self.next_char(true)? {
            Ok(c) => c,
            Err(e) => return Some(Err(e))
        };

        match c {
            '#' => self.lex_comment(begin_state).map(|r| r.1).transpose(),
            '"' | '`' => {
                // NOBODY
                // FUCKING CARES
                // ABOUT
                // YOUR
                // ALIASING
                // RULES
                let mut str_lexer = StringLexer::new(unsafe {
                    (self as *mut Self).as_mut_unchecked()
                });

                self.prev_char(true);
                Some(str_lexer.lex_string())
            },
            //'\'' => self.lex_char_lit(),
            '@' => Some(self.lex_modifier(begin_state)),
            c if c.is_ascii_alphabetic() => {
                self.reset_to_state(begin_state);
                Some(self.lex_alphabetic())
            },
            //c if is_mosaic_ident_start(&c) => self.lex_ident(),
            c if c.is_ascii_digit() => {
                let mut num_lexer = NumberLexer::new(unsafe {
                    (self as *mut Self).as_mut_unchecked()
                });

                self.prev_char(true);
                Some(num_lexer.lex_number())
            },
            c if LEGAL_CHARS.binary_search(&c).is_ok() =>
                Some(Ok(
                    (
                        Token::Symbol(c),
                        PositionRange::one_char(
                            self.reader.path.into(),
                            self.pos,
                            self.cur_context
                        )
                    ).into()
                )),
            c => todo!("Token beginning with {c} (in context {:?})", self.cur_context),
        }
    }
}
