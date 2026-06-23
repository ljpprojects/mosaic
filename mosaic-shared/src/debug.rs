use std::{fmt::{Debug, Display, Formatter}, num::{NonZeroU8, NonZeroU16}, path::PathBuf, sync::Arc};

use crate::states::Position;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenContext {
    StringTemplate,
    StringChars,
    StringEscape, // Only exists because of the BEHEMOTHS of string escapes
    StringEscapeParameterised,
    Path,
    Comment,
    NumberLiteral,
    CharLiteral,
    Modifier,
    Keyword,
    Identifier,
    LittleSpongeLivingInADumpster, // never actually constructed
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DebugPosition {
    pub file: PathBuf,

    pub offset: u16, // If your file is over 65.535kB it is too big

    // Lines & columns start at 1
    // If your file is more than 65535 lines long it is too big
    pub line: NonZeroU16,
    pub column: NonZeroU8,

    pub context: Option<TokenContext>,
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct PositionRange {
    pub start: DebugPosition,
    pub end: DebugPosition,
}

impl Display for PositionRange {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{} - {}:{}{m_C}",
            self.start.line, self.start.column,
            self.end.line, self.end.column,
            m_C = self.start.context
                .map(|c| format!(" in {c:?}"))
                .unwrap_or_default(),
        )
    }
}

impl Debug for PositionRange {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{F} @ {}:{} (+{s_O}) - {}:{} (+{e_O}){m_C}",
            self.start.line, self.start.column,
            self.end.line, self.end.column,
            F = self.start.file.display(),
            s_O = self.start.offset,
            e_O = self.end.offset,
            m_C = self.start.context
                .map(|c| format!(" in {c:?}"))
                .unwrap_or_default(),
        )
    }
}

impl PositionRange {
    pub fn one_char(
        file: PathBuf,
        pos: Position,
        context: Option<TokenContext>,
    ) -> Self {
        let pos = DebugPosition {
            file,
            offset: pos.offset,
            line: pos.line,
            column: pos.column,
            context,
        };

        Self {
            start: pos.clone(),
            end: pos,
        }
    }

    pub fn new(
        file: PathBuf,
        start: Position,
        end: Position,
        context: Option<TokenContext>,
    ) -> Self {
        let start = DebugPosition {
            file: file.clone(),
            offset: start.offset,
            line: start.line,
            column: start.column,
            context,
        };

        let end = DebugPosition {
            file,
            offset: end.offset,
            line: end.line,
            column: end.column,
            context,
        };

        Self { start, end, }
    }
}