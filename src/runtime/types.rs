use crate::parser::{ParseType};
use crate::runtime::values::RuntimeValue;

#[derive(Clone, Debug)]
pub enum Type<'a> {
    Null,
    Any,
    Ident(String),
    Path(&'a [String]),
    Array {
        element_type: &'a Type<'a>,
        size: usize,
    },
    Custom {
        match_fn: fn(&RuntimeValue) -> bool,
    }
}

impl<'a> Type<'a> {
    fn from_parse_type(parse_type: &'a ParseType) -> Self {
        match parse_type {
            ParseType::IdentType(i) => Type::Ident(i.clone()),
            ParseType::SpecificNumberType(n) => todo!("This is actually quite hard to implement :("),
            ParseType::ArrayType { element_type, length } => Type::Array { element_type: &Type::Any, size: *length },
            ParseType::PathType(path) => Type::Path(&*path),
        }
    }
}