use bigdecimal::{BigDecimal, Zero, num_bigint::BigInt};

use mosaic_shared::debug::{PositionRange, TokenContext};
use mosaic_shared::states::{LexerState, WithState};

use crate::lexer::LexOutput;
use crate::lexer::{StreamedLexer, errors::LexError, tokens::Token};

trait ActualScaleChangeExtension {
    /// As it is, with_scale will adjust the int value back
    /// We will skip this rather than dividing by a power of ten to
    /// reverse that
    ///
    /// If you look at the implementation of BigDecimal::with_scale:
    /// ```
    /// pub fn with_scale(&self, new_scale: i64) -> BigDecimal {
    ///     if self.int_val.is_zero() {
    ///         return BigDecimal::new(BigInt::zero(), new_scale);
    ///     }
    ///
    ///     match new_scale.cmp(&self.scale) {
    ///         Ordering::Greater => {
    ///             let scale_diff = new_scale - self.scale;
    ///             let int_val = &self.int_val * ten_to_the(scale_diff as u64); // <<<< A
    ///             BigDecimal::new(int_val, new_scale)
    ///         }
    ///         Ordering::Less => {
    ///             let scale_diff = self.scale - new_scale;
    ///             let int_val = &self.int_val / ten_to_the(scale_diff as u64);
    ///             BigDecimal::new(int_val, new_scale)
    ///         }
    ///         Ordering::Equal => self.clone(),
    ///     }
    /// }
    /// ```
    ///
    /// And look at line A, it adjusts the int_value so that (1).with_scale(2)
    /// would give 1.00, but we need it to give 0.01, so we skip it
    /// and adjust the scale directly, as the struct layout is like
    /// this:
    /// pub struct BigDecimal {
    ///     int_val: BigInt,
    ///     // A positive scale means a negative power of 10
    ///     scale: i64,
    /// }
    fn with_new_scale(&self, scale: i64) -> Self;
}

impl ActualScaleChangeExtension for BigDecimal {
    fn with_new_scale(&self, scale: i64) -> Self {
        let mut d = self.clone();
        let offset = size_of::<BigInt>();
        unsafe {
            *((&mut d) as *mut BigDecimal as *mut i64).byte_add(offset) = scale;
        };
        d
    }
}

/// A sub-lexer that specialises in the lexing of integer and float literals.
/// It supports base 2, 8, 10, and 16 integer and float literals.
///
/// Examples:
///
/// 0x8 is a base 16 integer literal
/// 0b1000 is a base 2 integer literal
/// 0o010 is a base 8 integer literal
///
/// 0x8.4 is a base 16 float literal (which has the value 8 * 16^0 + 4 * 16^-1, or 8.25)
/// 0o010.2 is a base 8 float literal (1 * 8^1 + 2 * 8^-1, 8 + 1/4 = 8.25)
/// 0b1000.01 is a base 2 float literal (2^3 + 2^-2, 8 + 1/4 = 8.25)
///
/// SHIT SCIENTIFIC NOTATION
///
/// 1e20 = 1 * 10^20 (results in an integer)
/// 0x1:e14 = 1 * 16^20
/// 0b1e1000 = 1 * 2^8
/// 0o010e4 = 1 * 8^4
///
/// 0x8.4:e2 = 8.25 * 16^2
///
/// The exponents can be negative btw (and you get a float literal)
///
/// WAIT FUCK e IS RESERVED IN HEX USE A COLON AFTER e IF IT ISNT AN EXPONENT
///
/// 0xde:adbe:e:f
///
/// SCRATCH THAT USE A COLON IF IT IS AN EXPONENT BUT BEFORE THE e
///
/// WAIT NVM ITS ALL p NOW FOR power (e is allowed but p is preferred)
///
/// 1p20 = 1 * 10^20 (results in an integer)
/// 0x1p14 = 1 * 16^20
/// 0b1p1000 = 1 * 2^8
/// 0o010p4 = 1 * 8^4
///
/// 0x8.4p2 = 8.25 * 16^2
///
/// Note: Integer literals are secretly Levetiracetam and thus are soluble in
/// Chloroform (see https://www.ebs.tga.gov.au/ebs/picmi/picmirepository.nsf/pdf?OpenAgent=&id=CP-2014-PI-03334-1). Put colons around the integer to dissolve it into
/// Chloroform solution, which can then be taken intravenously (by using a slim
/// left arrow into the patient).
/// A practical demonstration:
///
/// uptr<1984> <- :::::1997::::: (10 parts chloroform, 4 parts integer, 65
/// integer characters can be dissolved per 100 colons)
///
/// The implementation of std::ops::Inject for uptr is to perform addition.
///
/// The solution of chloroform is required its signature is:
///     fn Inject::inject(self: &.Inject, other: &.chem::ChloroformSolution)
///
/// The use of Levetiracetam has a chance to cause the program to develop
/// suicidal thoughts. The chloroform will kill it before it has a chance to act
/// (20% chance first injection, up by 10% each subsequent). If the chloroform
/// doesn't kill the program then it may kill itself, with variable but upwards
/// trending chances every Inject::inject invokation GLOBALLY.
///
/// END SECTION ABOUT LERETkFNwsg AND ENTER MUPIROCIN
///
/// "Any product remaining at the end of treatment should be discarded." MY FUCKING
/// ASS I HAVE IT STILL AND ITS BEEN 11 MONTHS (see https://www.ebs.tga.gov.au/ebs/picmi/picmirepository.nsf/pdf?OpenAgent&id=CP-2017-PI-02094-1)
///
/// "Common (approximately 2%): itching, burning, erythema, stinging, pain/swelling at site of
/// application and dryness. Less than 1% of patients discontinued therapy because of these local
/// reactions." WEAKLINGS
///
/// ALL HAIL C26H44O9
///
/// FLOAT LITERALS ARE A \{Schedule 4 – Prescription Only Medicine}
/// I AM A \{Schedule 7} ON DRUGS TAKE \{Schedule 5}
///
/// MOSAIC COMPILER IS \{Schedule 9} MEANING \{Fun} BUT IS ALSO \{Schedule 1}
///
/// I AM GOING TO SEND \{Gift = Schedule 6 Drug} TO YOUR HOUSE IN 2 \{Business Years}
pub struct NumberLexer;

impl<'a> NumberLexer {
    /// Lex a base 10 number assuming we already know that it won't be another
    /// base. It still expects all of the digits of the number to be unconsumed.
    ///
    /// Integer literals have arbitrary precision in token representation (the
    /// first stage of static analysis will reduce the width form u128 based on
    /// the strategy specified there, if the strategy doesn't specify an overflow
    /// strategy (e.g. creating some sort of BigInt object or equivalent) it will
    /// produce an error)
    ///
    /// Float literals are arbitrary-precision in their token representation. Like
    /// integers, the compiler will reduce the width based on their value, or
    /// construct some arbitrary precision object (e.g. BigDecimal or equivalent)
    /// if the strategy specifies to, otherwise it raises an error.
    ///
    /// By default this will emit an integer literal, unless it sees a fractional
    /// part (a full stop proceeded by numbers), in which case it emits a float
    /// literal.
    ///
    /// This also handles scientific notation and applies it at compile time.
    pub fn lex_base_10(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::NumberLiteral);

        // We don't need to store the digits as thats a waste of space, we can just
        // multiply whatever is already in this by 10 (or generally the base)
        // and add the new digit
        let mut integer_part = BigInt::ZERO;

        // Same deal here but in reverse, when we see a new fractional digit we
        // add the new digbit divided by ten (rather than mutliplying the total
        // by 10 and adding the digit).
        let mut fraction_part = BigDecimal::zero();

        // Same deal here
        // Since we have arbitrary precision we technically should have this be
        // arbitrary precision too but like... 10^(2^127 - 1) is UNFATHOMABLY large
        let mut exponent = 0i64;

        // Genuinely debating if I have 6 hours to spare (its 21:20) to do a run
        // through of EATEOT
        // OK
        // I have considered very carefully
        // I can do a few stages perhaps (it is 21:23 so I have 3-4 hours unless
        // I want to feel particularly shitty tomorrow).
        // no fuck that

        // right number lexing time

        // 0x0 = integer part
        // 0x1 = fraction part
        // 0x2 = exponent part
        // 0x4 = float override
        let mut state_flag = 0u8;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                break;
            };

            if next == 'p' || next == 'e' && state_flag & 0x10 == 0 {
                // We have an exponent part now
                state_flag = 2;
                continue;
            }

            // Negation is a unary operator and thus not the job of the lexer

            if next == '.' && state_flag & 4 == 0 {
                state_flag = 5; // Enter fractional part (4 | 1)
                continue;
            } else if next == '.' {
                // No fractional parts inside another fractional
                // No fractional exponents
                // Thus this is the start of a new token (probably a member access)
                lexer.prev_char(false);
                break;
            }

            if !next.is_ascii_digit() {
                lexer.prev_char(false);
                break;
            };

            let digit = next as i8 - '0' as i8;

            if state_flag == 0 {
                integer_part *= 10;
                integer_part += digit;
            } else if state_flag & 1 == 1 {
                fraction_part += BigDecimal::from(digit)
                    .with_new_scale(fraction_part.as_bigint_and_scale().1 + 1);
            } else if state_flag & 2 == 2 {
                exponent *= 10;
                exponent += digit as i64;
            }
        }

        eprintln!("frac {fraction_part}");

        // Combine our number into a BigInt/BigDecimal
        if state_flag & 4 == 0 && exponent >= 0 {
            // We have an integer (no fractional digits, float override, or
            // negative exponent
            let integer = integer_part * BigInt::from(10).pow(exponent as u32);

            return Ok(LexOutput(
                Token::Integer(integer),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        } else {
            // If any of those were true:
            //   state_flag & 4 == 4
            //   exponent < 0
            // Then we have a decimal

            // Negative scale = positive power of ten
            // Positive scale = negative power of ten
            let decimal = fraction_part + BigDecimal::from_bigint(integer_part, -exponent);

            return Ok(LexOutput(
                Token::Decimal(decimal),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        }
    }

    /// Lex a base 16 number assuming we already know that it won't be another
    /// base. It still expects all of the digits of the number to be unconsumed.
    ///
    /// The logic is basically the same as lex_number_base_10 but with adjustments
    /// made for the different base.
    pub fn lex_base_16(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::NumberLiteral);

        let mut integer_part = BigInt::ZERO;
        let mut fraction_part = BigDecimal::zero();
        let mut exponent = 0i64;

        // 0x0 = integer part
        // 0x1 = fraction part
        // 0x2 = exponent part
        // 0x4 = float override
        let mut state_flag = 0u8;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                break;
            };

            // e is not allowed as it is a hexadecimal digit
            if next == 'p' {
                // We have an exponent part now
                state_flag = 2;
                continue;
            }

            if next == '.' && state_flag & 4 == 0 {
                state_flag |= 5; // Enter fractional part
                continue;
            } else if next == '.' {
                lexer.prev_char(false);
                break;
            }

            if !next.is_ascii_hexdigit() {
                lexer.prev_char(false);
                break;
            };

            // 0 - 9 = digits
            // 17 - 22 = upper hex digits
            // 49 - 54 = lower hex digits
            let mut digit = next as i8 - '0' as i8;

            // Adjust upper/lowercase A-F to 10-15
            if digit >= 17 as i8 && digit <= 22 as i8 {
                digit -= 7;
            } else if digit >= 49 as i8 && digit <= 54 as i8 {
                digit -= 39;
            }

            if state_flag == 0 {
                integer_part <<= 4; // * 2^4
                integer_part += digit;
            } else if state_flag & 1 == 1 {
                fraction_part += BigDecimal::from(digit)
                    / BigDecimal::from(16).powi(fraction_part.fractional_digit_count() + 1);
            } else if state_flag & 2 == 2 {
                exponent <<= 4;
                exponent += digit as i64;
            }
        }

        // Combine our number into a BigInt/BigDecimal
        if fraction_part.fractional_digit_count() == 0 && exponent >= 0 {
            // We have an integer (no fractional digits, float override, or
            // negative exponent
            let integer = integer_part * BigInt::from(16).pow(exponent as u32);

            return Ok(LexOutput(
                Token::Integer(integer),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        } else {
            // Negative scale = positive power of ten
            // Positive scale = negative power of ten
            let decimal = (fraction_part + integer_part) * BigDecimal::from(16).powi(exponent);

            return Ok(LexOutput(
                Token::Decimal(decimal),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        }
    }

    /// Lex a base 8 number assuming we already know that it won't be another
    /// base. It still expects all of the digits of the number to be unconsumed.
    ///
    /// The logic is basically the same as lex_number_base_10 but with adjustments
    /// made for the different base.
    pub fn lex_base_8(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::NumberLiteral);

        let mut integer_part = BigInt::ZERO;
        let mut fraction_part = BigDecimal::zero();
        let mut exponent = 0i64;

        // 0x0 = integer part
        // 0x1 = fraction part
        // 0x2 = exponent part
        // 0x4 = float override
        let mut state_flag = 0u8;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                break;
            };

            if next == 'p' || next == 'e' {
                // We have an exponent part now
                state_flag = 2;
                continue;
            }

            if next == '.' && state_flag & 4 == 0 {
                state_flag |= 5; // Enter fractional part
                continue;
            } else if next == '.' {
                lexer.prev_char(false);
                break;
            }

            if !next.is_ascii_octdigit() {
                lexer.prev_char(false);
                break;
            };

            // 0 - 1 = digits
            let digit = next as i8 - '0' as i8;

            if state_flag == 0 {
                integer_part <<= 3; // * 2^3 = 8
                integer_part += digit;
            } else if state_flag & 1 == 1 {
                fraction_part += BigDecimal::from(digit)
                    / BigDecimal::from(8).powi(fraction_part.fractional_digit_count() + 1);
            } else if state_flag & 2 == 2 {
                exponent <<= 3;
                exponent += digit as i64;
            }
        }

        // Combine our number into a BigInt/BigDecimal
        if fraction_part.fractional_digit_count() == 0 && exponent >= 0 {
            // We have an integer (no fractional digits, float override, or
            // negative exponent
            let integer = integer_part * BigInt::from(8).pow(exponent as u32);

            return Ok(LexOutput(
                Token::Integer(integer),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        } else {
            let decimal = (fraction_part + integer_part) * BigDecimal::from(8).powi(exponent);

            return Ok(LexOutput(
                Token::Decimal(decimal),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        }
    }

    /// Lex a base 2 number assuming we already know that it won't be another
    /// base. It still expects all of the digits of the number to be unconsumed.
    ///
    /// The logic is basically the same as lex_number_base_10 but with adjustments
    /// made for the different base.
    pub fn lex_base_2(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<LexOutput, LexError> {
        lexer.cur_context = Some(TokenContext::NumberLiteral);

        let mut integer_part = BigInt::ZERO;
        let mut fraction_part = BigDecimal::zero();
        let mut exponent = 0i64;

        // 0x0 = integer part
        // 0x1 = fraction part
        // 0x2 = exponent part
        let mut state_flag = 0u8;

        loop {
            let Some(next) = lexer
                .next_char(false)
                .transpose()
                .inspect_err(|_| lexer.reset_to_state(begin_state))?
            else {
                break;
            };

            if next == 'p' || next == 'e' {
                // We have an exponent part now
                state_flag = 2;
                continue;
            }

            if next == '.' && state_flag & 1 == 0 {
                state_flag |= 1; // Enter fractional part
                continue;
            } else if next == '.' {
                lexer.prev_char(false);
                break;
            }

            if next != '0' && next != '1' {
                lexer.prev_char(false);
                break;
            };

            // 0 - 1 = digits
            let digit = next as i8 - '0' as i8;

            if state_flag == 0 {
                integer_part <<= 1; // * 2^1
                integer_part += digit;
            } else if state_flag & 1 == 1 {
                fraction_part += BigDecimal::from(digit)
                    / BigDecimal::from(2).powi(fraction_part.fractional_digit_count() + 1);
            } else if state_flag & 2 == 2 {
                exponent <<= 1;
                exponent += digit as i64;
            }
        }

        // Combine our number into a BigInt/BigDecimal
        if fraction_part.fractional_digit_count() == 0 && exponent >= 0 {
            // We have an integer (no fractional digits, float override, or
            // negative exponent
            let integer = integer_part * BigInt::from(2).pow(exponent as u32);

            return Ok(LexOutput(
                Token::Integer(integer),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        } else {
            let decimal = (fraction_part + integer_part) * BigDecimal::from(2).powi(exponent);

            return Ok(LexOutput(
                Token::Decimal(decimal),
                PositionRange::new(
                    lexer.reader.path.into(),
                    begin_state.pos,
                    lexer.pos,
                    lexer.cur_context,
                ),
                None,
            ))
            .inspect(|_| lexer.cur_context = begin_state.cur_context);
        }
    }

    /// Disambiguates the base of a number, returning the base and consuming any
    /// base prefixes.
    /// Returns either 2, 8, 10, or 16.
    fn disambiguate_base(lexer: &mut StreamedLexer<'a>) -> u8 {
        // If we see the 0x prefix the base is 16
        if lexer.expect_char_sequence("0x").is_ok() {
            16
        } else if lexer.expect_char_sequence("0o").is_ok() {
            // 0o = 8
            8
        } else if lexer.expect_char_sequence("0b").is_ok() {
            // 0b = 2
            2
        } else {
            // Anything else is base 10
            10
        }
    }

    pub fn lex_number(lexer: &mut StreamedLexer<'a>) -> Result<LexOutput, LexError> {
        let begin_state = lexer.state();

        // Dispatch to handlers based on base
        match Self::disambiguate_base(lexer) {
            2 => Self::lex_base_2(lexer, begin_state),
            8 => Self::lex_base_8(lexer, begin_state),
            10 => Self::lex_base_10(lexer, begin_state),
            16 => Self::lex_base_16(lexer, begin_state),
            _ => unreachable!("NumberLexer::disambiguate_base only returns 2, 8, 10, or 16"),
        }
    }
}

mod tests {
    use std::{
        num::{NonZeroU8, NonZeroU16},
        str::FromStr,
    };

    use bigdecimal::{BigDecimal, FromPrimitive, num_bigint::BigInt};
    use mosaic_shared::{
        debug::{PositionRange, TokenContext},
        reader::CharReader,
        states::Position,
    };

    use crate::lexer::{StreamedLexer, tokens::Token};

    #[test]
    pub fn number_lexer_base10() {
        let content = r#"1234567"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(1234567)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 7,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(8) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base16() {
        let content = r#"0xF"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(15)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 3,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(4) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base8() {
        let content = r#"0o22"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(18)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 4,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(5) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base2() {
        let content = r#"0b1001"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(9)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 6,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(7) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base10_pow() {
        let content = r#"123p3"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(123000)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 5,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(6) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base16_pow() {
        let content = r#"0x4p2"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(1024)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 5,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(6) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base8_pow() {
        let content = r#"0o20p2"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(1024)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 6,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(7) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base2_pow() {
        let content = r#"0b100p1000"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Integer(BigInt::from(1024)),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 10,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(11) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }

    #[test]
    pub fn number_lexer_base10_decimal() {
        let content = r#"123.4567"#;

        let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
        let mut lexer = StreamedLexer::new(reader);

        let result = lexer.next_token();
        let expected = Some(Ok((
            Token::Decimal(BigDecimal::from_str("123.4567").unwrap()),
            PositionRange::new(
                "-".into(),
                Position {
                    offset: 0,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(1) },
                },
                Position {
                    offset: 8,
                    line: unsafe { NonZeroU16::new_unchecked(1) },
                    column: unsafe { NonZeroU8::new_unchecked(9) },
                },
                Some(TokenContext::NumberLiteral),
            ),
        )
            .into()));

        assert_eq!(result, expected);
    }
}
