use std::{num::NonZeroU16, path::PathBuf};

use crate::{frontend::lexer::debug::{PositionRange, TokenContext}, states::Position};


pub enum LexError {
    InvalidChar(char, PositionRange),
    UnclosedString(PositionRange),
    TooManyLines(Option<TokenContext>),
    TooManyColumns(Option<TokenContext>, NonZeroU16),
    // if either TooManyLines/Columns occurs with this error prefer to raise them
    TooManyBytes(Option<TokenContext>),
    UnknownStringEscape(String, PositionRange),
    UnknownModifier(String, PositionRange),
    UnexpectedEOF(Option<TokenContext>),
    ExpectedModifier(PositionRange),
}