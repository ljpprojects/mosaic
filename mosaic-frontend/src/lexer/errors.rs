use mosaic_shared::debug::{PositionRange, TokenContext};
use std::num::NonZeroU16;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LexWarning {
    /// Raised when a minus appears without leading whitespace while lexing a number
    /// Corresponds to the `ambiguous-minus` warning
    ///
    /// For example, writing `5.4-2.` would have this error raised (you should write `5.4 - 2.`)
    /// It would also be raised when writing `1e3-1` (`1e3 - 1` should be written instead)
    VisuallyAmbiguousMinus(PositionRange),

    /// Raised when a keyword has mixed-case
    /// Corresponds to the `mixed-case-keyword` warning
    ///
    /// For example, writing `Import` would raise this error
    MixedCaseKeyword(PositionRange),
    Many(Box<[LexWarning]>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidChar(char, PositionRange),
    UnclosedString(PositionRange),
    TooManyLines(Option<TokenContext>),
    TooManyColumns(Option<TokenContext>, NonZeroU16),
    // if either TooManyLines/Columns occurs with this error prefer to raise
    // those instead
    TooManyBytes(Option<TokenContext>),
    UnknownStringEscape(String, PositionRange),
    UnmatchedDelimeter(char, PositionRange),
    TooMuchDepth(PositionRange),
    UnknownModifier(String, PositionRange),
    UnexpectedEOF(Option<TokenContext>),
    ExpectedCharacter(char, char, PositionRange),
    ExpectedModifier(PositionRange),
    ExpectedKeyword(PositionRange),
    ExpectedDigit(char, PositionRange),
    ByteLiteralOverflow(PositionRange),
    IntegerLiteralOverflow(PositionRange),
    FloatLiteralOverflow(PositionRange),
    ExpectCharacterIn(&'static [char], char, PositionRange),
    Many(Box<[LexError]>),
}