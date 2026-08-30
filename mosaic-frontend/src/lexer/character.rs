//! Character lexer

use std::num::{IntErrorKind, ParseIntError};

use mosaic_shared::{
    debug::{PositionRange, TokenContext},
    states::{LexerState, WithState},
};

use crate::lexer::{StreamedLexer, errors::LexError};

/// A sorted sequence of the legal escapes (their identifiers) in Mosaic for character literals.
pub const CHAR_ESCAPE_SEQUENCES: &[char] = &['\'', '0', '\\', 'e', 'n', 'o', 'r', 't', 'u', 'x'];

pub struct CharLexer;

impl<'a> CharLexer {
    pub fn lex_escape_parameterised(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
        escape_char: char,
    ) -> Result<char, LexError> {
        lexer.cur_context = Some(TokenContext::CharEscapeParameterised);

        match escape_char {
            'x' => {
                let mut digits = [0u8; 2];

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
                }

                Ok(u8::from_ascii_radix(&digits, 16).unwrap() as char)
                    .inspect(|_| lexer.cur_context = begin_state.cur_context)
            }
            'o' => {
                let mut digits = [0u8; 3];

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
                }

                let c = match u8::from_ascii_radix(&digits, 8) {
                    Ok(b) => b as char,
                    Err(e) => match e.kind() {
                        IntErrorKind::PosOverflow => {
                            return Err(LexError::ByteLiteralOverflow(PositionRange::new(
                                lexer.reader.path.into(),
                                begin_state.pos,
                                lexer.pos,
                                lexer.cur_context,
                            )))
                            .inspect_err(|_| lexer.reset_to_state(begin_state));
                        }
                        _ => unreachable!(),
                    },
                };

                Ok(c).inspect(|_| lexer.cur_context = begin_state.cur_context)
            }
            _ => panic!("Non-parameterised escape {escape_char}"),
        }
    }

    /// Lex an escape sequence in a character literal, assuming the opening apostrophe and slash have been consumed already
    pub fn lex_escape(
        lexer: &mut StreamedLexer<'a>,
        begin_state: LexerState<'a>,
    ) -> Result<char, LexError> {
        lexer.cur_context = Some(TokenContext::CharEscape);

        // All escape sequence identifierss are one character long
        // As with strings, '\ \' is a valid escape sequence, as is '\ 0', '\ n', etc., but you really shouldn't put whitespace between the slash and identifier
        let ident = match lexer.next_char(true) {
            Some(Ok(c)) => c,
            Some(Err(e)) => return Err(e).inspect_err(|_| lexer.reset_to_state(begin_state)),
            None => {
                return Err(LexError::UnexpectedEOF(lexer.cur_context))
                    .inspect_err(|_| lexer.reset_to_state(begin_state));
            }
        };

        // Unlike strings, character literal's contents are always known at compile-time, because a
        // templated character literal (theoretically '\{X}') would require the expression to be of type `char`, in which case you can just use the expression directly
        let result = match ident {
            '\'' => '\'',
            '0' => 0 as char,
            '\\' => '\\',
            'e' => '\x1b',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'o' | 'u' | 'x' => Self::lex_escape_parameterised(lexer, begin_state, ident)?, // Parameterised escapes
        };
    }
}
