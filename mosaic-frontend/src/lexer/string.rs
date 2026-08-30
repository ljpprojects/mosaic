use std::cell::RefCell;
use std::num::IntErrorKind;

use mosaic_shared::debug::{PositionRange, TokenContext};
use mosaic_shared::states::{LexerState, Position, WithState};

use crate::lexer::errors::LexError;
use crate::lexer::tokens::{StringEscape, StringInnards, StringPart, Token};
use crate::lexer::{LexOutput, StreamedLexer};

/// A sorted sequence of the legal escapes (their identifiers) in Mosaic.
pub const STR_ESCAPE_SEQUENCES: &[&str] = &[
    "\"", "'", "0", "\\", "ansi", "b", "bold", "code", "e", "n", "o", "r", "reset", "rgb", "t",
    "u", "x",
];

/// A sorted sequence of the legal escapes whose identifiers are one character
/// only.
pub const ONE_CHAR_STR_ESCAPE_SEQUENCES: &[char] =
    &['"', '\'', '0', '\\', 'e', 'n', 'o', 't', 'u', 'x'];

/// A sorted sequence of the starting character of escapes that can either be
/// one character or be many characters
pub const ONE_OR_MANY_CHAR_ESCAPE_SEQUENCE_STARTS: &[char] = &['b', 'r'];

/// Sub-lexer which is specialised in the lexing of strings.
pub struct StringLexer;

impl<'a> StringLexer {
    /// Lex a string template, assuming that the leading `\{` has been consumed
    /// already.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    fn lex_string_template(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<(StringPart, PositionRange), LexError> {
        lexer.cur_context = Some(TokenContext::StringTemplate);

        // We will just keep lexing until depth goes back to zero
        // If it doesnt (or we see a " while depth = 1) then the template is
        // missing a closing delimeter
        let mut depth = 1u8; // Start at 1 because \{ has been consumed already
        let mut tokens = Vec::<(Token, PositionRange)>::new();

        loop {
            let Some(next) = lexer.next_token() else {
                // Unmatched delimeter by EOF
                let e = Err(LexError::UnmatchedDelimeter(
                    '}',
                    PositionRange::new(
                        lexer.reader.path.into(),
                        begin_state.pos,
                        lexer.pos,
                        lexer.cur_context,
                    ),
                ));

                lexer.reset_to_state(begin_state);

                return e;
            };

            let LexOutput(next, npos, _) = match next {
                Ok(v) => v,
                Err(e) => {
                    lexer.reset_to_state(begin_state);
                    return Err(e);
                }
            };

            match next {
                // If the token is a '}' decrease depth
                Token::Symbol('}') => match depth.checked_sub(2) {
                    Some(nd) => {
                        depth = nd + 1;
                    }
                    None => {
                        // Depth is zero, template has closed
                        break;
                    }
                },

                // if the token is a '{' increase depth
                Token::Symbol('{') => match depth.checked_add(1) {
                    Some(nd) => depth = nd,
                    None => {
                        // Depth exceeded 255

                        return Err(LexError::TooMuchDepth(PositionRange::new(
                            lexer.reader.path.into(),
                            begin_state.pos,
                            lexer.pos,
                            lexer.cur_context,
                        )))
                        .inspect_err(|_| lexer.reset_to_state(begin_state));
                    }
                },

                _ => tokens.push((next, npos)),
            }
        }

        Ok((
            StringPart::Template(tokens.into_boxed_slice()),
            PositionRange::new(
                lexer.reader.path.into(),
                begin_state.pos,
                lexer.pos,
                lexer.cur_context,
            ),
        ))
        .inspect(|_| lexer.cur_context = begin_state.cur_context)
    }

    pub fn is_escape_sequence_start(c: char) -> bool {
        // Sorted sequence of the legal escape starts
        const LEGAL_ESCAPE_STARTS: &[char] = &[
            '"', '\'', '0', '\\', 'a', 'b', 'c', 'e', 'n', 'o', 'r', 't', 'u', 'x',
        ];

        LEGAL_ESCAPE_STARTS.binary_search(&c).is_ok()
    }

    pub fn is_escape_sequence_part(c: char) -> bool {
        // Sorted sequence of the legal escape starts
        const LEGAL_ESCAPE_PARTS: &[char] = &['b', 'd', 'e', 'g', 'i', 'l', 'n', 'o', 's', 't'];

        LEGAL_ESCAPE_PARTS.binary_search(&c).is_ok()
    }

    /// Lex a comples parameterised string escape, one of:
    /// - `\ansi`
    /// - `\code`
    /// - `\rgb`
    ///
    /// This function assumes the escape name has been consumed already.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their `begin_state` parameterised to allow for proper state
    /// restoration on error.
    pub fn lex_escape_complex_parameterised(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
        escape_name: &str,
    ) -> Result<(StringPart, PositionRange), LexError> {
        lexer.cur_context = Some(TokenContext::StringEscapeParameterised);

        match escape_name {
            "ansi" => {
                // The syntax is \ansi({C}: {Arg1}; {Arg2}; ...; {ArgN})

                // Consume opening parenthesis
                let _open_paren = lexer
                    .expect_char('(')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let Some(code) = lexer
                    .next_char(true)
                    .transpose()
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?
                else {
                    return Err(LexError::UnexpectedEOF(lexer.cur_context));
                };

                let _colon = lexer
                    .expect_char(':')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let mut args = Vec::<u8>::new();

                loop {
                    let mut digits = [0u8; 2];
                    for i in 0..2 {
                        let Some(next) = lexer
                            .next_char(true)
                            .transpose()
                            .inspect_err(|_| lexer.reset_to_state(begin_state))?
                        else {
                            return Err(LexError::UnexpectedEOF(lexer.cur_context))
                                .inspect_err(|_| lexer.reset_to_state(begin_state));
                        };

                        if !next.is_ascii_digit() {
                            lexer.prev_char(true);

                            // Would totally use LLVM as the backend btw if it
                            // didn't support so many targets (I am only going to
                            // write so many scripts to generate wrappers over
                            // raw syscalls and am only going to write the
                            // stdlib for so many architectures)

                            return Err(LexError::ExpectedDigit(
                                next,
                                PositionRange::one_char(
                                    lexer.reader.path.into(),
                                    lexer.pos,
                                    lexer.cur_context,
                                ),
                            ))
                            .inspect_err(|_| lexer.reset_to_state(begin_state));
                        }

                        digits[i] = next as u8;
                    }

                    let arg = u8::from_ascii_radix(&digits, 10).unwrap();

                    args.push(arg);

                    if let Some(Ok(next)) = lexer.next_char(true) {
                        if next == ')' {
                            break;
                        }

                        if next == ';' {
                            continue;
                        }

                        lexer.prev_char(true);
                    }
                }

                Ok((
                    StringPart::Escape(StringEscape::ANSIOther(code, args.into_boxed_slice())),
                    PositionRange::new(
                        lexer.reader.path.into(),
                        begin_state.pos,
                        lexer.pos,
                        lexer.cur_context,
                    ),
                ))
                .inspect(|_| lexer.cur_context = begin_state.cur_context)
            }
            "code" => {
                // The syntax is \code(fg/bg; {Code})

                // Consume opening parenthesis
                let _open_paren = lexer
                    .expect_char('(')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let is_foreground = match lexer.expect_char_sequence("fg") {
                    Ok(_) => true,
                    Err(_) => lexer
                        .expect_char_sequence("bg")
                        .inspect_err(|_| lexer.reset_to_state(begin_state))
                        .map(|_| false)?,
                };

                let _semicolon = lexer
                    .expect_char(';')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let startpos: Position = lexer.pos;

                let mut digits = [0u8; 3];
                for i in 0..3 {
                    let Some(next) = lexer
                        .next_char(true)
                        .transpose()
                        .inspect_err(|_| lexer.reset_to_state(begin_state))?
                    else {
                        return Err(LexError::UnexpectedEOF(lexer.cur_context))
                            .inspect_err(|_| lexer.reset_to_state(begin_state));
                    };

                    if !next.is_ascii_digit() {
                        lexer.prev_char(true);

                        // Would totally use LLVM as the backend btw if it
                        // didn't support so many targets (I am only going to
                        // write so many scripts to generate wrappers over
                        // raw syscalls and am only going to write the
                        // stdlib for so many architectures)

                        return Err(LexError::ExpectedDigit(
                            next,
                            PositionRange::one_char(
                                lexer.reader.path.into(),
                                lexer.pos,
                                lexer.cur_context,
                            ),
                        ))
                        .inspect_err(|_| lexer.reset_to_state(begin_state));
                    }

                    digits[i] = next as u8;
                }

                let Ok(code) = u8::from_ascii_radix(&digits, 10) else {
                    return Err(LexError::ByteLiteralOverflow(PositionRange::new(
                        lexer.reader.path.into(),
                        startpos,
                        lexer.pos,
                        lexer.cur_context,
                    )))
                    .inspect_err(|_| lexer.reset_to_state(begin_state));
                };

                let _close_paren = lexer
                    .expect_char(')')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                if is_foreground {
                    Ok((
                        StringPart::Escape(StringEscape::ANSICodeFG(code)),
                        PositionRange::new(
                            lexer.reader.path.into(),
                            begin_state.pos,
                            lexer.pos,
                            lexer.cur_context,
                        ),
                    ))
                    .inspect(|_| lexer.cur_context = begin_state.cur_context)
                } else {
                    Ok((
                        StringPart::Escape(StringEscape::ANSICodeBG(code)),
                        PositionRange::new(
                            lexer.reader.path.into(),
                            begin_state.pos,
                            lexer.pos,
                            lexer.cur_context,
                        ),
                    ))
                    .inspect(|_| lexer.cur_context = begin_state.cur_context)
                }
            }
            "rgb" => {
                // The syntax is \rgb(fg/bg; {R}; {G}; {B})

                // Consume opening parenthesis
                let _open_paren = lexer
                    .expect_char('(')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let is_foreground = match lexer.expect_char_sequence("fg") {
                    Ok(_) => true,
                    Err(_) => lexer
                        .expect_char_sequence("bg")
                        .inspect_err(|_| lexer.reset_to_state(begin_state))
                        .map(|_| false)?,
                };

                let _semicolon = lexer
                    .expect_char(';')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                let mut startpos: Option<Position> = None;

                let mut red = 0u8;
                let mut green = 0u8;
                let mut blue = 0u8;

                for i in 0..3 {
                    let mut digits = [0u8; 3];
                    for j in 0..3 {
                        if j == 0 {
                            startpos = Some(lexer.pos);
                        }

                        let Some(next) = lexer
                            .next_char(true)
                            .transpose()
                            .inspect_err(|_| lexer.reset_to_state(begin_state))?
                        else {
                            return Err(LexError::UnexpectedEOF(lexer.cur_context))
                                .inspect_err(|_| lexer.reset_to_state(begin_state));
                        };

                        if !next.is_ascii_digit() {
                            lexer.prev_char(true);

                            // Would totally use LLVM as the backend btw if it
                            // didn't support so many targets (I am only going to
                            // write so many scripts to generate wrappers over
                            // raw syscalls and am only going to write the
                            // stdlib for so many architectures)

                            return Err(LexError::ExpectedDigit(
                                next,
                                PositionRange::one_char(
                                    lexer.reader.path.into(),
                                    lexer.pos,
                                    lexer.cur_context,
                                ),
                            ))
                            .inspect_err(|_| lexer.reset_to_state(begin_state));
                        }

                        digits[j] = next as u8;
                    }

                    let Ok(value) = u8::from_ascii_radix(&digits, 10) else {
                        return Err(LexError::ByteLiteralOverflow(PositionRange::new(
                            lexer.reader.path.into(),
                            startpos.unwrap(),
                            lexer.pos,
                            lexer.cur_context,
                        )))
                        .inspect_err(|_| lexer.reset_to_state(begin_state));
                    };

                    match i {
                        0 => red = value,
                        1 => green = value,
                        2 => blue = value,
                        _ => unreachable!(),
                    }

                    if let Some(Ok(next)) = lexer.next_char(true) {
                        if next == ')' {
                            break;
                        }

                        if next == ',' {
                            continue;
                        }

                        lexer.prev_char(true);
                    }
                }

                if is_foreground {
                    Ok((
                        StringPart::Escape(StringEscape::ANSIRGBFG(red, green, blue)),
                        PositionRange::new(
                            lexer.reader.path.into(),
                            begin_state.pos,
                            lexer.pos,
                            lexer.cur_context,
                        ),
                    ))
                    .inspect(|_| lexer.cur_context = begin_state.cur_context)
                } else {
                    Ok((
                        StringPart::Escape(StringEscape::ANSIRGBBG(red, green, blue)),
                        PositionRange::new(
                            lexer.reader.path.into(),
                            begin_state.pos,
                            lexer.pos,
                            lexer.cur_context,
                        ),
                    ))
                    .inspect(|_| lexer.cur_context = begin_state.cur_context)
                }
            }
            _ => unreachable!(),
        }
    }

    /// Lex a simple parameterised string escape (`\x`, `\o`, or `\u`).
    ///
    /// This function assumes the `\x`, `\o`, or `\u` has been consumed already.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    pub fn lex_escape_simple_parameterised(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
        escape_char: char,
    ) -> Result<(StringPart, PositionRange), LexError> {
        lexer.cur_context = Some(TokenContext::StringEscapeParameterised);

        match escape_char {
            'x' => {
                let mut digits = [0u8; 2];
                let mut n = 0;

                for i in 0..2 {
                    let Some(next) = lexer
                        .next_char(false)
                        .transpose()
                        .inspect_err(|_| lexer.reset_to_state(begin_state))?
                    else {
                        return Err(LexError::UnexpectedEOF(lexer.cur_context));
                    };

                    if !next.is_ascii_hexdigit() {
                        lexer.prev_char(false);
                        break;
                    }

                    digits[i] = next as u8;
                    n += 1;
                }

                Ok((
                    StringPart::Escape(StringEscape::Byte(
                        u8::from_ascii_radix(&digits[..n], 16).unwrap(), // An overflow is impossible with 2 hex digits, so we can skip handling error cases here
                    )),
                    PositionRange::new(
                        lexer.reader.path.into(),
                        begin_state.pos,
                        lexer.pos,
                        lexer.cur_context,
                    ),
                ))
            }
            'o' => {
                let mut digits = [0u8; 3];
                let mut n = 0;

                let digits_start = lexer.pos;
                let mut digits_end = digits_start;

                for i in 0..3 {
                    let Some(next) = lexer
                        .next_char(false)
                        .transpose()
                        .inspect_err(|_| lexer.reset_to_state(begin_state))?
                    else {
                        break;
                    };

                    if !next.is_ascii_octdigit() {
                        lexer.prev_char(false);
                        break;
                    }

                    digits[i] = next as u8;
                    digits_end = lexer.pos;
                    n += 1;
                }

                let byte = match u8::from_ascii_radix(&digits[..n], 8) {
                    Ok(b) => b,
                    Err(e) => match e.kind() {
                        IntErrorKind::PosOverflow => {
                            return Err(LexError::ByteLiteralOverflow(PositionRange::new(
                                lexer.reader.path.into(),
                                digits_start,
                                digits_end,
                                lexer.cur_context,
                            )))
                            .inspect_err(|_| lexer.reset_to_state(begin_state));
                        }
                        _ => unreachable!(),
                    },
                };

                Ok((
                    StringPart::Escape(StringEscape::Byte(byte)),
                    PositionRange::new(
                        lexer.reader.path.into(),
                        begin_state.pos,
                        lexer.pos,
                        lexer.cur_context,
                    ),
                ))
                .inspect(|_| lexer.cur_context = begin_state.cur_context)
            }
            'u' => {
                lexer
                    .expect_char('{')
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                // Parse up to 6 hex digits
                let mut digits = [0u8; 6];
                let mut n = 0; // How many digits we have actually used

                let digits_start = lexer.pos;
                let mut digits_end = digits_start;

                for i in 0..6 {
                    let Some(next) = lexer
                        .next_char(false)
                        .transpose()
                        .inspect_err(|_| lexer.reset_to_state(begin_state))?
                    else {
                        break;
                    };

                    if next == '}' {
                        break;
                    }

                    if !next.is_ascii_hexdigit() {
                        lexer.prev_char(false);
                        return Err(LexError::ExpectedHexDigit(
                            next,
                            PositionRange::new(
                                lexer.reader.path.into(),
                                lexer.pos,
                                lexer.pos,
                                lexer.cur_context,
                            ),
                        ))
                        .inspect_err(|_| lexer.reset_to_state(begin_state));
                    }

                    digits[i] = next as u8;
                    digits_end = lexer.pos;
                    n += 1;
                }

                let codepoint = u32::from_ascii_radix(&digits[..n], 16).unwrap();
                let Some(c) = char::from_u32(codepoint) else {
                    return Err(LexError::InvalidCodepoint(
                        codepoint,
                        PositionRange::new(
                            lexer.reader.path.into(),
                            digits_start,
                            digits_end,
                            lexer.cur_context,
                            // Do I live just to be tormented by the idea of something I can never reach?
                        ),
                    ))
                    .inspect_err(|_| lexer.reset_to_state(begin_state));
                };

                Ok((
                    StringPart::Escape(StringEscape::UnicodeCharacter(c)),
                    PositionRange::new(
                        lexer.reader.path.into(),
                        begin_state.pos,
                        lexer.pos,
                        lexer.cur_context,
                    ),
                ))
            }
            _ => unreachable!(),
        }
    }

    /// Lex an escape in a string, assuming the leading `\` is already consumed.
    /// If the escape is actually a template, then a StringPart::Template is
    /// returned, otherwise a StringPart::Escape is returned.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    fn lex_string_escape(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<(StringPart, PositionRange), LexError> {
        lexer.cur_context = Some(TokenContext::StringEscape);

        // Get the next character
        // We ignore whitespace so that `\ r` is `\r` and `\ code(4)` is
        // `\code(4)` deal with it
        let Some(next) = lexer.next_char(true) else {
            return Err(LexError::UnexpectedEOF(lexer.cur_context))
                .inspect_err(|_| lexer.reset_to_state(begin_state));
        };

        // Only needed to avoid issues with borrow checker
        let start = match next {
            Ok(n) => n,
            Err(e) => return Err(e).inspect_err(|_| lexer.reset_to_state(begin_state)),
        };

        let mut escape_seq = String::new();
        escape_seq.push(start);

        if start == '{' {
            return Self::lex_string_template(lexer, begin_state);
        } else if !StringLexer::is_escape_sequence_start(start) {
            // Just parse any escape part that is either
            //   - StringLexer::is_escape_sequence_start
            //   - StringLexer::is_escape_sequence_part
            //   - char::is_ascii_alphanumeric
            //
            // We will reject it anyway so it doesn't really matter the level of
            // garbage we accept

            escape_seq.push(start);

            loop {
                let Some(next) = lexer
                    .next_char(false)
                    .transpose()
                    .inspect_err(|_| lexer.reset_to_state(begin_state))?
                else {
                    break;
                };

                if !StringLexer::is_escape_sequence_start(next)
                    && !StringLexer::is_escape_sequence_part(next)
                    && !next.is_ascii_alphanumeric()
                {
                    lexer.prev_char(false);
                    break;
                }

                escape_seq.push(next);
            }

            return Err(LexError::UnknownStringEscape(
                escape_seq,
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
            ))
            .inspect_err(|_| lexer.reset_to_state(begin_state));
        };

        // Actually lex an escape sequence unless we know it is one character
        if ONE_CHAR_STR_ESCAPE_SEQUENCES.binary_search(&start).is_err() {
            loop {
                let Some(next) = lexer.next_char(false).transpose()? else {
                    break;
                };

                if next == ':'
                    && ONE_OR_MANY_CHAR_ESCAPE_SEQUENCE_STARTS
                        .binary_search(&start)
                        .is_ok()
                {
                    // : here delimits the end of a one char escape sequence
                    // that could be longer
                    break;
                }

                if !StringLexer::is_escape_sequence_part(next) {
                    lexer.prev_char(false);
                    break;
                }

                escape_seq.push(next);
            }
        }

        // Now we check if the escape sequence is one of our legal ones
        // (the loop allows the order to be scrambled)
        let Ok(escape_seq) = STR_ESCAPE_SEQUENCES
            .binary_search(&&*escape_seq)
            .map(|i| STR_ESCAPE_SEQUENCES[i])
        else {
            // Gotos would be somewhat nice here to avoid constant repition of
            // this without needing to create a mini-DSL (macro) or function
            return Err(LexError::UnknownStringEscape(
                escape_seq,
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
            ))
            .inspect_err(|_| lexer.reset_to_state(begin_state));
        };

        match escape_seq {
            "ansi" | "code" | "rgb" => {
                Self::lex_escape_complex_parameterised(lexer, begin_state, escape_seq)
            }
            "o" | "u" | "x" => Self::lex_escape_simple_parameterised(
                lexer,
                begin_state,
                escape_seq.chars().next().unwrap(),
            )
            .inspect_err(|_| lexer.reset_to_state(begin_state)),
            _ => Ok((
                StringPart::Escape(StringEscape::try_from_escape_seq(escape_seq).unwrap()),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
            )),
        }
    }

    /// Lex a raw string. Raw strings will lex anything and everything until it
    /// encounters a ` not proceeded by another ` (as `` inside of a raw string
    /// is the escape for backticks, deal with it).
    ///
    /// This function assumes the leading backtick has already been consumed.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    pub fn lex_raw_string(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::StringChars);

        let mut contents = String::new();

        let content_start_state = lexer.state();
        let mut content_end_state = content_start_state;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                return Err(LexError::UnexpectedEOF(lexer.cur_context));
            };

            if next == '`' {
                // Peek the next char, if it is another backtick then we just
                // insert one backtick
                if let Some('`') = lexer.reader.peek_next_char() {
                    contents.push('`');
                    lexer.next_char(false);
                    continue;
                }

                break;
            }

            contents.push(next);
            content_end_state = lexer.state();
        }

        let part = StringPart::Static(contents);
        let innards = StringInnards {
            parts: Box::new([(
                part,
                PositionRange::new(
                    lexer.reader.path.into(),
                    content_start_state.pos,
                    content_end_state.pos,
                    lexer.cur_context,
                ),
            )]),
        };

        Ok((
            Token::String(innards),
            PositionRange::new(
                lexer.reader.path.into(),
                begin_state.pos,
                lexer.pos,
                lexer.cur_context,
            ),
        )
            .into())
        .inspect(|_| lexer.cur_context = begin_state.cur_context)
    }

    /// Lex a raw string or normal string.
    pub fn lex_string(lexer: &mut StreamedLexer<'a>) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::StringChars);

        let begin_state = lexer.state();

        let used_delim = lexer
            .expect_char_in(&['"', '`'])
            .inspect_err(|_| lexer.reset_to_state(begin_state))?;

        let raw_mode_enabled = used_delim == '`';
        if raw_mode_enabled {
            return Self::lex_raw_string(lexer, begin_state);
        }

        let mut parts = Vec::<(StringPart, PositionRange)>::new();
        let mut acc = String::new(); // Accumulated static content

        let mut content_start_state = lexer.state();
        let mut content_end_state = content_start_state;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                return Err(LexError::UnexpectedEOF(lexer.cur_context));
            };

            match next {
                '"' => {
                    if acc.len() > 0 {
                        let part = StringPart::Static(acc.clone());

                        parts.push((
                            part,
                            PositionRange::new(
                                lexer.reader.path.into(),
                                content_start_state.pos,
                                content_end_state.pos,
                                lexer.cur_context,
                            ),
                        ));
                    }

                    break;
                }
                '\\' => {
                    // push the static content if there is any
                    if acc.len() > 0 {
                        let part = StringPart::Static(acc.clone());

                        parts.push((
                            part,
                            PositionRange::new(
                                lexer.reader.path.into(),
                                content_start_state.pos,
                                content_end_state.pos,
                                lexer.cur_context,
                            ),
                        ));

                        acc.clear();
                    }

                    let escape_or_template = Self::lex_string_escape(lexer, content_end_state)
                        .inspect_err(|_| lexer.reset_to_state(begin_state))?;

                    parts.push(escape_or_template);

                    lexer.cur_context = Some(TokenContext::StringChars);
                    content_start_state = lexer.state();
                    content_end_state = content_start_state;
                }
                _ => {
                    acc.push(next);
                    content_end_state = lexer.state();
                }
            };
        }

        let innards = StringInnards {
            parts: parts.into_boxed_slice(),
        };

        Ok((
            Token::String(innards),
            PositionRange::new(
                lexer.reader.path.into(),
                begin_state.pos,
                lexer.pos,
                lexer.cur_context,
            ),
        )
            .into())
        .inspect(|_| lexer.cur_context = begin_state.cur_context)
    }
}
