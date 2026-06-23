use std::num::{NonZeroU8, NonZeroU16};

use mosaic_shared::debug::{PositionRange, TokenContext};
use mosaic_shared::states::Position;
use mosaic_shared::reader::CharReader;

use crate::lexer::StreamedLexer;
use crate::lexer::tokens::{StringEscape, StringInnards, StringPart, Token};

// ################################################################
// ##                                                            ##
// ##    StringLexer tests                                       ##
// ##                                                            ##
// ##    Test all functions of the StringLexer in the            ##
// ##    successful code path specifically.                      ##
// ##                                                            ##
// ################################################################

#[test]
pub fn string_lexer_static() {
    let content = r#""lmnop""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([(
                StringPart::Static("lmnop".to_string()),
                PositionRange::new(
                    "-".into(),
                    Position {
                        offset: 1,
                        line: unsafe { NonZeroU16::new_unchecked(1) },
                        column: unsafe { NonZeroU8::new_unchecked(2) },
                    },
                    Position {
                        offset: 6,
                        line: unsafe { NonZeroU16::new_unchecked(1) },
                        column: unsafe { NonZeroU8::new_unchecked(7) },
                    },
                    Some(TokenContext::StringChars)
                )
            )])
        }),
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
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

#[test]
pub fn string_lexer_raw() {
    let content = r#"`\notescape \{nottemplate} this is anything " and everything ' `` thats an escape for a backtick`"#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([(
                StringPart::Static("\\notescape \\{nottemplate} this is anything \" and everything ' ` thats an escape for a backtick".to_string()),
                PositionRange::new(
                    "-".into(),
                    Position {
                        offset: 1,
                        line: unsafe { NonZeroU16::new_unchecked(1) },
                        column: unsafe { NonZeroU8::new_unchecked(2) },
                    },
                    Position {
                        offset: 96,
                        line: unsafe { NonZeroU16::new_unchecked(1) },
                        column: unsafe { NonZeroU8::new_unchecked(97) },
                    },
                    Some(TokenContext::StringChars)
                )
            )])
        }),
        PositionRange::new(
            "-".into(),
            Position {
                offset: 0,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            Position {
                offset: 97,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(98) },
            },
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

#[test]
pub fn string_lexer_simple_escape() {
    let content = r#""\n""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([
                (
                    StringPart::Escape(StringEscape::Newline),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 1,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(2) },
                        },
                        Position {
                            offset: 3,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(4) },
                        },
                        Some(TokenContext::StringEscape)
                    )
                )
            ])
        }),
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
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

#[test]
pub fn string_lexer_simple_escapes() {
    let content = r#""lmnop\nololo\tlollipop""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([
                (
                    StringPart::Static("lmnop".to_string()),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 1,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(2) },
                        },
                        Position {
                            offset: 6,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(7) },
                        },
                        Some(TokenContext::StringChars)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::Newline),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 6,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(7) },
                        },
                        Position {
                            offset: 8,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(9) },
                        },
                        Some(TokenContext::StringEscape)
                    )
                ),
                (
                    StringPart::Static("ololo".to_string()),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 8,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(9) },
                        },
                        Position {
                            offset: 13,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(14) },
                        },
                        Some(TokenContext::StringChars)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::Tab),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 13,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(14) },
                        },
                        Position {
                            offset: 15,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(16) },
                        },
                        Some(TokenContext::StringEscape)
                    )
                ),
                (
                    StringPart::Static("lollipop".to_string()),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 15,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(16) },
                        },
                        Position {
                            offset: 23,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(24) },
                        },
                        Some(TokenContext::StringChars)
                    )
                ),
            ])
        }),
        PositionRange::new(
            "-".into(),
            Position {
                offset: 0,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            Position {
                offset: 24,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(25) },
            },
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

#[test]
pub fn string_lexer_simple_parameterised_escapes() {
    let content = r#""\x41\u{0041}""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([
                (
                    StringPart::Escape(StringEscape::Byte(65)),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 1,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(2) },
                        },
                        Position {
                            offset: 5,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(6) },
                        },
                        Some(TokenContext::StringEscapeParameterised)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::UnicodeCharacter('A')),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 5,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(6) },
                        },
                        Position {
                            offset: 13,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(14) },
                        },
                        Some(TokenContext::StringEscapeParameterised)
                    )
                )
            ])
        }),
        PositionRange::new(
            "-".into(),
            Position {
                offset: 0,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            Position {
                offset: 14,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(15) },
            },
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

pub fn string_lexer_complex_parameterised_escapes() {
    let content = r#""\rgb(fg; 255, 000, 000)\rgb(bg; 255, 255, 255)lmnop\reset\bold\ansi(m: 32)""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([
                (
                    StringPart::Escape(StringEscape::ANSIRGBFG(255, 0, 0)),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 1,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(2) },
                        },
                        Position {
                            offset: 24,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(25) },
                        },
                        Some(TokenContext::StringEscapeParameterised)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::ANSIRGBBG(255, 255, 255)),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 24,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(25) },
                        },
                        Position {
                            offset: 47,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(48) },
                        },
                        Some(TokenContext::StringEscapeParameterised)
                    )
                ),
                (
                    StringPart::Static("lmnop".to_string()),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 47,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(48) },
                        },
                        Position {
                            offset: 52,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(53) },
                        },
                        Some(TokenContext::StringChars)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::ANSIResetAll),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 52,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(53) },
                        },
                        Position {
                            offset: 58,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(59) },
                        },
                        Some(TokenContext::StringEscape)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::ANSIBold),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 58,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(59) },
                        },
                        Position {
                            offset: 63,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(64) },
                        },
                        Some(TokenContext::StringEscape)
                    )
                ),
                (
                    StringPart::Escape(StringEscape::ANSIOther('m', Box::new([32]))),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 63,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(64) },
                        },
                        Position {
                            offset: 75,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(76) },
                        },
                        Some(TokenContext::StringEscapeParameterised)
                    )
                ),
            ])
        }),
        PositionRange::new(
            "-".into(),
            Position {
                offset: 0,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            Position {
                offset: 76,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(77) },
            },
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

#[test]
pub fn string_lexer_templates() {
    // The lexer only tokenises a few things right now
    // Technically this counts as a lexer test too
    let content = r#""\{import}""#;

    let reader = CharReader::static_bytes(Box::from(content.as_bytes()));
    let mut lexer = StreamedLexer::new(reader);

    let result = lexer.next_token();
    let expected = Some(Ok((
        Token::String(StringInnards {
            parts: Box::new([
                (
                    StringPart::Template(Box::new([
                        (
                            Token::Keyword("import"),
                            PositionRange::new(
                                "-".into(),
                                Position {
                                    offset: 3,
                                    line: unsafe { NonZeroU16::new_unchecked(1) },
                                    column: unsafe { NonZeroU8::new_unchecked(4) },
                                },
                                Position {
                                    offset: 9,
                                    line: unsafe { NonZeroU16::new_unchecked(1) },
                                    column: unsafe { NonZeroU8::new_unchecked(10) },
                                },
                                Some(TokenContext::Keyword)
                            )
                        )
                    ])),
                    PositionRange::new(
                        "-".into(),
                        Position {
                            offset: 1,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(2) },
                        },
                        Position {
                            offset: 10,
                            line: unsafe { NonZeroU16::new_unchecked(1) },
                            column: unsafe { NonZeroU8::new_unchecked(11) },
                        },
                        Some(TokenContext::StringTemplate)
                    )
                )
            ])
        }),
        PositionRange::new(
            "-".into(),
            Position {
                offset: 0,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(1) },
            },
            Position {
                offset: 11,
                line: unsafe { NonZeroU16::new_unchecked(1) },
                column: unsafe { NonZeroU8::new_unchecked(12) },
            },
            Some(TokenContext::StringChars)
        )
    ).into()));

    assert_eq!(result, expected);
}

// ################################################################
// ##                                                            ##
// ##    StreamedLexer tests                                     ##
// ##                                                            ##
// ##    Test tokenising functions of the Lexer in the           ##
// ##    successful code path specifically.                      ##
// ##                                                            ##
// ################################################################