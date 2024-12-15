use crate::compiler::qbe::types::QbeType as Type;
use crate::compiler::GenerationError;
use crate::parser::{ParseError, TypeBound};
use crate::utils::Indirection;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;

#[derive(Clone)]
pub enum QbeGenerationError<'a> {
    DoubleDefinition(String),
    UndefinedSymbol(String),
    UndefinedLibrary(PathBuf),
    InvalidCast(Type<'a>, Type<'a>),
    CannotIndex(Type<'a>),
    /// symbol, expected, got
    MismatchedType(String, Type<'a>, Type<'a>),
    OutOfBounds(String, usize),
    CannotIterate(Indirection<Type<'a>>),
    UnmetBound(String, TypeBound, usize),
    GenericsDisallowed(String),
    ParseError(ParseError)
}

impl Error for QbeGenerationError<'_> {}
impl GenerationError for QbeGenerationError<'_> {}

impl Debug for QbeGenerationError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for QbeGenerationError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DoubleDefinition(name) => {
                write!(f, "E000: Attempted to define symbol more than once: {name}")
            }
            Self::UndefinedSymbol(name) => {
                write!(f, "E001: Attempted to reference undefined symbol: {name}")
            }
            Self::UndefinedLibrary(path) => write!(f, "Attempted to use undefined library: {path:?}"),
            Self::InvalidCast(from, to) => {
                write!(f, "E002: Invalid cast from type {from} to type {to}")
            }
            Self::MismatchedType(s, e, g) => write!(f, "E003: Mismatched types (in {s}); expected {e}, got {g}."),
            Self::CannotIndex(t) => write!(f, "E004: Cannot index type {t}"),
            Self::OutOfBounds(s, i) => write!(f, "E005: Attempted to access out-of-bounds index {i} (of {s})"),
            Self::CannotIterate(t) => write!(f, "E006: Cannot iterate over un-iterable type {t}."),
            Self::UnmetBound(s, bound, i) => write!(f, "E007: Bound not met of arg {i} of function {s}: {bound}"),
            Self::GenericsDisallowed(s) => write!(f, "E008: Generics disallowed in symbol {s}"),
            Self::ParseError(e) => write!(f, "Parse error: {e}")
        }
    }
}

pub type QbeGenerationResult<'a, T> = Result<T, QbeGenerationError<'a>>;
