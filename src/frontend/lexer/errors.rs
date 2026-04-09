use std::{num::NonZeroU16, path::PathBuf};

use crate::{frontend::lexer::debug::{PositionRange, TokenContext}, states::Position};


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
    ExpectedDigit(char, PositionRange),
    ByteLiteralOverflow(PositionRange),
    ExpectCharacterIn(&'static [char], char, PositionRange),
}