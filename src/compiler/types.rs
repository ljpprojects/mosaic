use crate::compiler::errors::{GenerationError, GenerationResult};
use crate::compiler::CodeGen;
use crate::parser::ParseType;
use crate::utils::Indirection;
use qbe::Value;
use std::fmt::Display;
use std::ops::Deref;
use std::str::FromStr;

#[derive(Debug, Clone)]
pub enum Type {
    Integer8,
    Integer16,
    Integer32,
    Integer64,
    Float64,
    Float32,
    Unsigned(Indirection<Type>),
    Pointer(Indirection<Type>),
    NullVoid,
    Boolean,

    /// Equivalent to the `*N[T]` type
    FatPointer(Indirection<Type>, u32),

    /// Equivalent to the `*:E[T]` type
    TerminatedSlice(Indirection<Type>, Value),
}

pub const CSTRING_TYPES: &[&str] = &["Pc", "E0_c"];

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Integer8 => write!(f, "c"),
            Type::Integer16 => write!(f, "s"),
            Type::Integer32 => write!(f, "i"),
            Type::Integer64 => write!(f, "l"),
            Type::Float64 => write!(f, "d"),
            Type::Float32 => write!(f, "f"),
            Type::Pointer(t) => write!(f, "P{t}"),
            Type::Unsigned(t) => write!(f, "U{t}"),
            Type::NullVoid => write!(f, "v"),
            Type::Boolean => write!(f, "b"),
            Type::FatPointer(t, l) => write!(f, "F{l}_{t}"),
            Type::TerminatedSlice(t, term) => write!(f, "E{term}_{t}"),
        }
    }
}

impl<'a> Type {
    /// A lossy conversion from a [Type] to a [qbe::Type].
    /// Cannot be reversed.
    pub fn into_qbe(self) -> qbe::Type<'a> {
        match self {
            Type::Integer8 | Type::NullVoid | Type::Boolean => qbe::Type::SignedByte,
            Type::Integer16 => qbe::Type::SignedHalfword,
            Type::Integer32 => qbe::Type::Word,
            Type::Integer64 => qbe::Type::Long,
            Type::Pointer(_) => qbe::Type::Long,
            Type::Float64 => qbe::Type::Double,
            Type::Float32 => qbe::Type::Single,
            Type::Unsigned(t) => match t.deref().clone() {
                Type::Integer8 => qbe::Type::UnsignedByte,
                Type::Integer16 => qbe::Type::UnsignedHalfword,
                t => t.into_qbe(),
            },
            Type::FatPointer(_, _) => qbe::Type::Long,
            Type::TerminatedSlice(_, _) => qbe::Type::Long,
        }
    }

    /// Equivalent to [Type::fmt], but fat pointers have their length erased.
    pub fn to_cmp_string(&self) -> String {
        match self {
            Type::FatPointer(t, _) => format!("F{t}"),
            _ => format!("{self}"),
        }
    }

    /// Equivalent to [Type::fmt], but "generics" are erased.
    pub fn to_type_erased_string(&self) -> String {
        match self {
            Type::FatPointer(_, _) => "F".to_string(),
            Type::TerminatedSlice(_, _) => "E".to_string(),
            Type::Pointer(_) => "P".to_string(),
            Type::Unsigned(_) => "U".to_string(),
            _ => format!("{self}"),
        }
    }

    pub fn into_qbe_abi(self) -> qbe::Type<'a> {
        self.into_qbe().into_abi()
    }
}

impl FromStr for Type {
    type Err = GenerationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.chars().into_iter();

        match iter.next().unwrap() {
            'c' => Ok(Type::Integer8),
            's' => Ok(Type::Integer16),
            'i' => Ok(Type::Integer32),
            'l' => Ok(Type::Integer64),
            'v' => Ok(Type::NullVoid),
            'b' => Ok(Type::Boolean),
            'f' => Ok(Type::Float32),
            'd' => Ok(Type::Float64),
            'F' => {
                let mut len = String::new();

                while let Some(c) = iter.next()
                    && c != '_'
                {
                    len += c.to_string().as_str();
                }

                let inner = Type::from_str(iter.collect::<String>().as_str())?;

                Ok(Type::FatPointer(
                    Indirection::new(inner),
                    len.parse().unwrap(),
                ))
            }
            'E' => {
                let mut term = String::new();

                while let Some(c) = iter.next()
                    && c != '_'
                {
                    term += c.to_string().as_str();
                }

                let inner = Type::from_str(iter.collect::<String>().as_str())?;

                Ok(Type::TerminatedSlice(
                    Indirection::new(inner),
                    Value::Const(term.parse().unwrap()),
                ))
            }
            'U' => {
                let inner = Type::from_str(iter.collect::<String>().as_str())?;

                Ok(Type::Unsigned(Indirection::new(inner)))
            }
            'P' => {
                let inner = Type::from_str(iter.collect::<String>().as_str())?;

                Ok(Type::Pointer(Indirection::new(inner)))
            }
            c => unimplemented!("Unknown type {}", c),
        }
    }
}

pub struct TypeGenerator;

impl TypeGenerator {
    pub fn new() -> Self {
        Self
    }

    pub fn generate_type(parse: ParseType, mut cg: CodeGen) -> GenerationResult<Type> {
        match parse {
            ParseType::IdentType(ref i) => match cg.types.get(i) {
                Some(t) => Ok(t.clone()),
                None => Err(GenerationError::UndefinedSymbol(i.clone())),
            },
            ParseType::ArrayType { .. } => todo!(),
            ParseType::PointerType(to) => Ok(Type::Pointer(Indirection::new(Self::generate_type(
                to.deref().clone(),
                cg,
            )?))),
            ParseType::FatPointerType(t, l) => Ok(Type::FatPointer(
                t.map_result(|p| Self::generate_type(p, cg))?,
                l,
            )),
            ParseType::TerminatedSlice(t, e) => Ok(Type::TerminatedSlice(
                t.map_result(|p| Self::generate_type(p, cg.clone()))?,
                cg.generate_independent_expr(e.deref().clone())?.1,
            )),
        }
    }
}

mod tests {
    use crate::compiler::types::Type;
    use std::str::FromStr;

    #[test]
    fn types_from_mangled() {
        let string = "E0_c";

        println!("{}", Type::from_str(string).unwrap());
    }
}
