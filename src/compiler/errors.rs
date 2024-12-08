use crate::compiler::errors::GenerationError::UndefinedLibrary;
use crate::compiler::types::Type;
use crate::parser::AstNode;
use std::error::Error;
use std::fmt::{write, Display};
use std::path::PathBuf;

#[derive(Debug)]
pub enum GenerationError {
    DoubleDefinition(String),
    UndefinedSymbol(String),
    UndefinedLibrary(PathBuf),
    InvalidCast(Type, Type),
    CannotIndex(Type),
    /// symbol, expected, got
    MismatchedType(String, Type, Type)
}

impl Display for GenerationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GenerationError::DoubleDefinition(name) => {
                write!(f, "E000: Attempted to define symbol more than once: {name}")
            }
            GenerationError::UndefinedSymbol(name) => {
                write!(f, "E001: Attempted to reference undefined symbol: {name}")
            }
            UndefinedLibrary(path) => write!(f, "Attempted to use undefined library: {path:?}"),
            GenerationError::InvalidCast(from, to) => {
                write!(f, "E002: Invalid cast from type {from} to type {to}")
            }
            GenerationError::MismatchedType(s, e, g) => write!(f, "E003: Mismatched types (in {s}); expected {e}, got {g}."),
            GenerationError::CannotIndex(t) => write!(f, "E004: Cannot index type {t}"),
        }
    }
}

impl Error for GenerationError {}

pub type GenerationResult<T> = Result<T, GenerationError>;
