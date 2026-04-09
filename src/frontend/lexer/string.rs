use crate::{exit::{nondeterminism, weird_exit}, frontend::lexer::{StreamedLexer, debug::{PositionRange, TokenContext}, errors::LexError, tokens::{StringEscape, StringPart, Token}}, states::{LexerState, Position, WithState}};

/// A sorted sequence of the legal escapes (their identifiers) in Mosaic.
pub const LEGAL_ESCAPE_SEQUENCES: &[&str] = &[
    "\"", "'", "0", "\\", "ansi", "b", "bold", "code",
    "e", "n", "o", "r", "reset", "rgb", "t", "u", "x"
];

/// Sub-lexer which is specialised in the lexing of strings.
pub struct StringLexer<'a> {
    lexer: &'a mut StreamedLexer<'a>,
}

impl<'a> StringLexer<'a> {
    pub fn new(lexer: &'a mut StreamedLexer<'a>) -> Self {
        Self {
            lexer,
        }
    }

    /// Lex a string template, assuming that the leading `\{` has been consumed
    /// already.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    fn lex_string_template(&mut self, begin_state: LexerState<'a>) -> Result<(StringPart, PositionRange), LexError> {
        self.lexer.cur_context = Some(TokenContext::StringTemplate);

        // We will just keep lexing until depth goes back to zero
        // If it doesnt (or we see a " while depth = 1) then the template is
        // missing a closing delimeter
        let mut depth = 1u8; // Start at 1 because \{ has been consumed already
        let mut tokens = Vec::<Token>::new();

        loop {
            let Some(next) = self.lexer.next_token() else {
                // Unmatched delimeter by EOF
                let e = Err(LexError::UnmatchedDelimeter(
                    '}',
                    PositionRange::new(
                        self.lexer.reader.path.into(),
                        begin_state.pos,
                        self.lexer.pos,
                        self.lexer.cur_context,
                    )
                ));

                self.lexer.reset_to_state(begin_state);

                return e
            };

            let (next, _) = match next {
                Ok(v) => v,
                Err(e) => {
                    self.lexer.reset_to_state(begin_state);
                    return Err(e)
                },
            };

            match next {
                // If the token is a '}' decrease depth
                Token::Symbol('}') => match depth.checked_sub(1) {
                    Some(nd) => depth = nd,
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

                        return Err(LexError::TooMuchDepth(
                            PositionRange::new(
                                self.lexer.reader.path.into(),
                                begin_state.pos,
                                self.lexer.pos,
                                self.lexer.cur_context,
                            )
                        )).inspect_err(|_|  self.lexer.reset_to_state(begin_state))
                    }
                },

                _ => tokens.push(next),
            }
        };

        Ok((
            StringPart::Template(tokens.into_boxed_slice()),
            PositionRange::new(
                self.lexer.reader.path.into(),
                begin_state.pos,
                self.lexer.pos,
                self.lexer.cur_context
            )
        )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
    }

    pub fn is_escape_sequence_start(c: char) -> bool {
        // Sorted sequence of the legal escape starts
        const LEGAL_ESCAPE_STARTS: &[char] = &[
            '"', '\'', '0', '\\', 'a', 'b', 'c',
            'e', 'n', 'o', 'r', 't', 'u', 'x'
        ];

        LEGAL_ESCAPE_STARTS.binary_search(&c).is_ok()
    }

    pub fn is_escape_sequence_part(c: char) -> bool {
        // Sorted sequence of the legal escape starts
        const LEGAL_ESCAPE_PARTS: &[char] = &[
            'b', 'd', 'e', 'g', 'i', 'l', 'n', 'o', 's', 't'
        ];

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
        &mut self,
        begin_state: LexerState<'a>,
        escape_name: &str,
    ) -> Result<(StringPart, PositionRange), LexError> {
        self.lexer.cur_context = Some(TokenContext::StringEscapeParameterised);

        match escape_name {
            "ansi" => {
                // The syntax is \ansi({C}: {Arg1}; {Arg2}; ...; {ArgN})

                // Consume opening parenthesis
                let _open_paren = self.lexer.expect_char('(')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let Some(code) = self.lexer.next_char(true)
                    .transpose()
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                else {
                    return Err(LexError::UnexpectedEOF(self.lexer.cur_context))
                };

                let _colon = self.lexer.expect_char(':')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let mut args = Vec::<u8>::new();

                loop {
                    let mut digits = [0u8; 2];
                    for i in 0..2 {
                        let Some(next) = self.lexer.next_char(true)
                            .transpose()
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                        else {
                            return Err(LexError::UnexpectedEOF(self.lexer.cur_context))
                                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                        };

                        if !next.is_ascii_digit() {
                            self.lexer.prev_char(true);

                            // Would totally use LLVM as the backend btw if it
                            // didn't support so many targets (I am only going to
                            // write so many scripts to generate wrappers over
                            // raw syscalls and am only going to write the
                            // stdlib for so many architectures)

                            return Err(LexError::ExpectedDigit(
                                next,
                                PositionRange::one_char(
                                    self.lexer.reader.path.into(),
                                    self.lexer.pos,
                                    self.lexer.cur_context
                                )
                            ))
                                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                        }

                        digits[i] = next as u8;
                    }

                    let arg = u8::from_ascii_radix(&digits, 10).unwrap();

                    args.push(arg);

                    if let Some(Ok(next)) = self.lexer.next_char(true) {
                        if next == ')' {
                            break
                        }

                        if next == ';' {
                            continue
                        }

                        self.lexer.prev_char(true);
                    }
                }

                Ok((
                    StringPart::Escape(
                        StringEscape::ANSIOther(code, args.into_boxed_slice())
                    ),
                    PositionRange::new(
                        self.lexer.reader.path.into(),
                        begin_state.pos,
                        self.lexer.pos,
                        self.lexer.cur_context
                    )
                )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
            }
            "code" => {
                // The syntax is \code(fg/bg; {Code})

                // Consume opening parenthesis
                let _open_paren = self.lexer.expect_char('(')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let is_foreground = match self.lexer.expect_char_sequence("fg") {
                    Ok(_) => true,
                    Err(_) => {
                        self.lexer.expect_char_sequence("bg")
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                            .map(|_| false)?
                    }
                };

                let _semicolon = self.lexer.expect_char(';')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let mut startpos: Option<Position> = None;

                let mut digits = [0u8; 3];
                for i in 0..3 {
                    if i == 0 {
                        startpos = Some(self.lexer.pos);
                    }

                    let Some(next) = self.lexer.next_char(true)
                        .transpose()
                        .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                    else {
                        return Err(LexError::UnexpectedEOF(self.lexer.cur_context))
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                    };

                    if !next.is_ascii_digit() {
                        self.lexer.prev_char(true);

                        // Would totally use LLVM as the backend btw if it
                        // didn't support so many targets (I am only going to
                        // write so many scripts to generate wrappers over
                        // raw syscalls and am only going to write the
                        // stdlib for so many architectures)

                        return Err(LexError::ExpectedDigit(
                            next,
                            PositionRange::one_char(
                                self.lexer.reader.path.into(),
                                self.lexer.pos,
                                self.lexer.cur_context
                            )
                        ))
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                    }

                    digits[i] = next as u8;
                }

                let Ok(code) = u8::from_ascii_radix(&digits, 10) else {
                    return Err(LexError::ByteLiteralOverflow(
                        PositionRange::new(
                            self.lexer.reader.path.into(),
                            startpos.unwrap(),
                            self.lexer.pos,
                            self.lexer.cur_context
                        )
                    )).inspect_err(|_| self.lexer.reset_to_state(begin_state))
                };

                let _close_paren = self.lexer.expect_char(')')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                if is_foreground {
                    Ok((
                        StringPart::Escape(
                            StringEscape::ANSICodeFG(code)
                        ),
                        PositionRange::new(
                            self.lexer.reader.path.into(),
                            begin_state.pos,
                            self.lexer.pos,
                            self.lexer.cur_context
                        )
                    )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
                } else {
                    Ok((
                        StringPart::Escape(
                            StringEscape::ANSICodeBG(code)
                        ),
                        PositionRange::new(
                            self.lexer.reader.path.into(),
                            begin_state.pos,
                            self.lexer.pos,
                            self.lexer.cur_context
                        )
                    )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
                }
            }
            "rgb" => {
                // The syntax is \rgb(fg/bg; {R}; {G}; {B})

                // Consume opening parenthesis
                let _open_paren = self.lexer.expect_char('(')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let is_foreground = match self.lexer.expect_char_sequence("fg") {
                    Ok(_) => true,
                    Err(_) => {
                        self.lexer.expect_char_sequence("bg")
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                            .map(|_| false)?
                    }
                };

                let _semicolon = self.lexer.expect_char(';')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                let mut startpos: Option<Position> = None;

                let mut red = 0u8;
                let mut green = 0u8;
                let mut blue = 0u8;

                for i in 0..3 {
                    let mut digits = [0u8; 3];
                    for j in 0..3 {
                        if j == 0 {
                            startpos = Some(self.lexer.pos);
                        }

                        let Some(next) = self.lexer.next_char(true)
                            .transpose()
                            .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                        else {
                            return Err(LexError::UnexpectedEOF(self.lexer.cur_context))
                                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                        };

                        if !next.is_ascii_digit() {
                            self.lexer.prev_char(true);

                            // Would totally use LLVM as the backend btw if it
                            // didn't support so many targets (I am only going to
                            // write so many scripts to generate wrappers over
                            // raw syscalls and am only going to write the
                            // stdlib for so many architectures)

                            return Err(LexError::ExpectedDigit(
                                next,
                                PositionRange::one_char(
                                    self.lexer.reader.path.into(),
                                    self.lexer.pos,
                                    self.lexer.cur_context
                                )
                            ))
                                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
                        }

                        digits[j] = next as u8;
                    }

                    let Ok(value) = u8::from_ascii_radix(&digits, 10) else {
                        return Err(LexError::ByteLiteralOverflow(
                            PositionRange::new(
                                self.lexer.reader.path.into(),
                                startpos.unwrap(),
                                self.lexer.pos,
                                self.lexer.cur_context
                            )
                        )).inspect_err(|_| self.lexer.reset_to_state(begin_state))
                    };

                    match i {
                        0 => red = value,
                        1 => green = value,
                        2 => blue = value,
                        _ => unreachable!()
                    }

                    if let Some(Ok(next)) = self.lexer.next_char(true) {
                        if next == ')' {
                            break
                        }

                        if next == ',' {
                            continue
                        }

                        self.lexer.prev_char(true);
                    }
                }

                let _close_paren = self.lexer.expect_char(')')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                if is_foreground {
                    Ok((
                        StringPart::Escape(
                            StringEscape::ANSIRGBFG(red, green, blue)
                        ),
                        PositionRange::new(
                            self.lexer.reader.path.into(),
                            begin_state.pos,
                            self.lexer.pos,
                            self.lexer.cur_context
                        )
                    )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
                } else {
                    Ok((
                        StringPart::Escape(
                            StringEscape::ANSIRGBBG(red, green, blue)
                        ),
                        PositionRange::new(
                            self.lexer.reader.path.into(),
                            begin_state.pos,
                            self.lexer.pos,
                            self.lexer.cur_context
                        )
                    )).inspect(|_| self.lexer.cur_context = begin_state.cur_context)
                }
            }
            _ => unreachable!()
        }
    }

    /// Lex a simple parameterised string escape (`\x`, `\o`, or `\u`).
    ///
    /// This function assumes the `\x`, `\o`, or `\u` has been consumed already.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    pub fn lex_string_escape_simple_parameterised(
        &mut self,
        begin_state: LexerState<'a>,
        escape_char: char,
    ) -> Result<(StringPart, PositionRange), LexError> {
        self.lexer.cur_context = Some(TokenContext::StringEscapeParameterised);

        match escape_char {
            'x' => {
                let mut digits = [0u8; 2];

                for i in 0..2 {
                    let Some(next) = self.lexer.next_char(false)
                        .transpose()
                        .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                    else {
                        break;
                    };

                    if !next.is_ascii_hexdigit() {
                        self.lexer.prev_char(false);
                        break;
                    }

                    digits[i] = next as u8;
                }

                Ok((
                    StringPart::Escape(StringEscape::Byte(
                        u8::from_ascii_radix(&digits, 16).unwrap()
                    )),
                    PositionRange::new(
                        self.lexer.reader.path.into(),
                        begin_state.pos,
                        self.lexer.pos,
                        self.lexer.cur_context
                    )
                ))
            },
            'o' => {
                let mut digits = [0u8; 3];

                for i in 0..3 {
                    let Some(next) = self.lexer.next_char(false)
                        .transpose()
                        .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                    else {
                        break;
                    };

                    if !next.is_ascii_octdigit() {
                        self.lexer.prev_char(false);
                        break;
                    }

                    digits[i] = next as u8;
                }

                Ok((
                    StringPart::Escape(StringEscape::Byte(
                        u8::from_ascii_radix(&digits, 8).inspect_err(
                            |_| nondeterminism() // You don't know that a byte must be less than 256???? HOW ABOUT WE FUCK UP THE WHOLE COMPILER
                        ).unwrap_or_default() // Lol f nondeterminism doesnt mess it up immediately make it a null byte
                    )),
                    PositionRange::new(
                        self.lexer.reader.path.into(),
                        begin_state.pos,
                        self.lexer.pos,
                        self.lexer.cur_context
                    )
                ))
            },
            'u' => {
                self.lexer.expect_char('{')
                    .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

                // Parse 4 hex digits
                let mut digits = [0u8; 4];
                let mut n = 0; // How many digits we have used

                for i in 0..4 {
                    let Some(next) = self.lexer.next_char(false)
                        .transpose()
                        .inspect_err(|_| self.lexer.reset_to_state(begin_state))?
                    else {
                        break;
                    };

                    if !next.is_ascii_hexdigit() {
                        self.lexer.prev_char(false);
                        break;
                    }

                    if next == '}' && n == 4 {
                        break;
                    } else if next == '}' {
                        // Very quickly exit the program for no fucking reason
                        // Untraceably so
                        // weird_exit is basically SIGSEGV on command
                        weird_exit()
                    }

                    digits[i] = next as u8;
                    n += 1;
                }

                let c = char::from_u32(u32::from_be_bytes(digits)).unwrap_or_else(|| {
                    nondeterminism();
                    '\0'
                });

                Ok((
                    StringPart::Escape(StringEscape::UnicodeCharacter(c)),
                    PositionRange::new(
                        self.lexer.reader.path.into(),
                        begin_state.pos,
                        self.lexer.pos,
                        self.lexer.cur_context
                    )
                ))
            },
            _ => unreachable!()
        }
    }

    /// Lex an escape in a string, assuming the leading `\` is already consumed.
    /// If the escape is actually a template, then a StringPart::Template is
    /// returned, otherwise a StringPart::Escape is returned.
    ///
    /// Note: All functions that assume any external state modification must
    /// have their begin_state parameterised to allow for proper state
    /// restoration on error.
    fn lex_string_escape(&mut self, begin_state: LexerState<'a>) -> Result<(StringPart, PositionRange), LexError> {
        self.lexer.cur_context = Some(TokenContext::StringEscape);

        // Get the next character
        // We ignore whitespace so that `\ r` is `\r` and `\ code(4)` is
        // `\code(4)` deal with it
        let Some(next) = self.lexer.next_char(true) else {
            return Err(LexError::UnexpectedEOF(self.lexer.cur_context))
                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
        };

        // Only needed to avoid issues with borrow checker
        let start = match next {
            Ok(n) => n,
            Err(e) => return Err(e)
                .inspect_err(|_| self.lexer.reset_to_state(begin_state))
        };

        let mut escape_seq = String::new();

        if start == '{' {
            self.lexer.reset_to_state(begin_state.clone());
            return self.lex_string_template(begin_state);
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
                let Some(next) = self.lexer.next_char(false).transpose()? else {
                    break;
                };

                if !StringLexer::is_escape_sequence_start(next) && !StringLexer::is_escape_sequence_part(next) && !next.is_ascii_alphanumeric() {
                    self.lexer.prev_char(false);
                    break;
                }

                escape_seq.push(next);
            }

            return Err(LexError::UnknownStringEscape(
                escape_seq,
                PositionRange::new(
                    self.lexer.reader.path.into(),
                    begin_state.pos,
                    self.lexer.pos,
                    self.lexer.cur_context
                )
            )).inspect_err(|_| self.lexer.reset_to_state(begin_state))
        };

        // Actually lex an escape sequence
        let mut rej_flag = false;
        loop {
            let Some(next) = self.lexer.next_char(false).transpose()? else {
                break;
            };

            if (!StringLexer::is_escape_sequence_part(next))
                || rej_flag && (
                    !StringLexer::is_escape_sequence_start(next)
                    && !next.is_ascii_alphanumeric()
                )
            {
                if !rej_flag {
                    rej_flag = true;
                    continue;
                }

                self.lexer.prev_char(false);
                break;
            }

            escape_seq.push(next);
        }

        // One of the characters inside the escape was invalid
        if rej_flag {
            return Err(LexError::UnknownStringEscape(
                escape_seq,
                PositionRange::new(
                    self.lexer.reader.path.into(),
                    begin_state.pos,
                    self.lexer.pos,
                    self.lexer.cur_context
                )
            )).inspect_err(|_| self.lexer.reset_to_state(begin_state))
        }

        // Now we check if the escape sequence is one of our legal ones
        // (the previous checks allow the order to be scrambled)
        let Ok(escape_seq) = LEGAL_ESCAPE_SEQUENCES
            .binary_search(&&*escape_seq)
            .map(|i| LEGAL_ESCAPE_SEQUENCES[i])
        else {
            // Gotos would be somewhat nice here to avoid constant repition of
            // this without needing to create a mini-DSL (macro) or function
            return Err(LexError::UnknownStringEscape(
                escape_seq,
                PositionRange::new(
                    self.lexer.reader.path.into(),
                    begin_state.pos,
                    self.lexer.pos,
                    self.lexer.cur_context
                )
            )).inspect_err(|_| self.lexer.reset_to_state(begin_state))
        };

        match escape_seq {
            "ansi" | "code" | "rgb" =>
                self.lex_escape_complex_parameterised(
                    begin_state,
                    escape_seq
                ),
            "o" | "u" | "x" =>
                self.lex_string_escape_simple_parameterised(
                    begin_state,
                    escape_seq.chars().next().unwrap()
                ),
            _ => Ok((
                StringPart::Escape(
                    StringEscape::try_from_escape_seq(escape_seq)
                        .unwrap()
                ),
                PositionRange::new(
                    self.lexer.reader.path.into(),
                    begin_state.pos,
                    self.lexer.pos,
                    self.lexer.cur_context
                )
            ))
        }
    }



    pub fn lex_string(&mut self) -> Result<(Token, PositionRange), LexError> {
        let begin_state = self.lexer.state();

        let used_delim = self.lexer.expect_char_in(&['"', '`'])
            .inspect_err(|_| self.lexer.reset_to_state(begin_state))?;

        let raw_mode_enabled = used_delim == '`';
        if raw_mode_enabled {
            return self.lex_raw_string(begin_state);
        }


    }
}