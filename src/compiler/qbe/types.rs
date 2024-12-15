use std::collections::HashMap;
use crate::compiler::qbe::errors::{QbeGenerationError, QbeGenerationResult};
use crate::compiler::qbe::values::QbeValue;
use crate::compiler::qbe::QbeGenerator;
use crate::compiler::{Generator, Value, ValueType};
use crate::parser::{ParseType, TypeBound};
use crate::utils::Indirection;
use qbe::TypeDef;
use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::str::FromStr;

#[derive(Clone)]
pub enum QbeType<'a> {
    Integer8,
    Integer16,
    Integer32,
    Integer64,
    Float64,
    Float32,
    Unsigned(Indirection<Self>),
    Pointer(Indirection<Self>),
    NullVoid,
    Boolean,
    Generic(String, Option<TypeBound>),

    /// Equivalent to the `*N[T]` type
    FatPointer(Indirection<Self>, u32),

    /// Equivalent to the `*:E[T]` type
    TerminatedSlice(Indirection<Self>, Indirection<QbeValue<'a>>),
    
    Aggregate(TypeDef<'a>, Indirection<Self>),
}

pub const CSTRING_TYPES: &[&str] = &["Pc", "E0_c"];

impl<'a> ValueType<'a> for QbeType<'a> {
    type Gen = QbeGenerator<'a>;
    
    fn size(&self) -> u64 {
        self.clone().into_qbe(false).size()
    }

    fn matches_bound(&self, bound: TypeBound, generator: &'a mut Self::Gen, allowed_tgs: &HashMap<String, Option<TypeBound>>) -> QbeGenerationResult<'a, bool> {
        match bound {
            TypeBound::Iterator(ref ty) => {
                match self {
                    QbeType::FatPointer(t, ..) => Ok(t.deref().clone() == TypeGenerator::generate_type(ty.get(), generator, allowed_tgs)?),
                    QbeType::TerminatedSlice(t, _) => Ok(t.deref().clone() == TypeGenerator::generate_type(ty.get(), generator, allowed_tgs)?),
                    QbeType::Aggregate(_, i) => i.matches_bound(bound, generator, allowed_tgs),
                    _ => Ok(false)
                }
            }
            TypeBound::Not(t) => self.matches_bound(t.deref().clone(), generator, allowed_tgs).map(|b| !b),
            TypeBound::Compound(bounds) => {
                for bound in bounds {
                    let matches = self.matches_bound(bound, unsafe { (generator as *mut Self::Gen).as_mut().unwrap() }, allowed_tgs)?;
                    if !matches {
                        return Ok(false);
                    }
                }

                Ok(true)
            },
        }
    }

    fn from_iter<I: Iterator<Item=char>>(iter: &mut I) -> Result<Self, QbeGenerationError<'a>> {
        match iter.next().unwrap() {
            'c' => Ok(QbeType::Integer8),
            's' => Ok(QbeType::Integer16),
            'i' => Ok(QbeType::Integer32),
            'l' => Ok(QbeType::Integer64),
            'v' => Ok(QbeType::NullVoid),
            'b' => Ok(QbeType::Boolean),
            'f' => Ok(QbeType::Float32),
            'd' => Ok(QbeType::Float64),
            'F' => {
                let mut len = String::new();

                while let Some(c) = iter.next()
                    && c != '_'
                {
                    len += c.to_string().as_str();
                }

                let inner = QbeType::from_str(iter.collect::<String>().as_str())?;

                Ok(QbeType::FatPointer(
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

                let inner = QbeType::from_str(iter.collect::<String>().as_str())?;

                Ok(QbeType::TerminatedSlice(
                    Indirection::new(inner),
                    Indirection::new(QbeValue::byte(term.parse().unwrap())),
                ))
            }
            'U' => {
                let inner = QbeType::from_str(iter.collect::<String>().as_str())?;

                Ok(QbeType::Unsigned(Indirection::new(inner)))
            }
            'P' => {
                let inner = QbeType::from_str(iter.collect::<String>().as_str())?;

                Ok(QbeType::Pointer(Indirection::new(inner)))
            }
            c => Err(QbeGenerationError::UndefinedSymbol(c.to_string())),
        }
    }
}

impl PartialEq for QbeType<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

impl Debug for QbeType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer8 => write!(f, "i8"),
            Self::Integer16 => write!(f, "i16"),
            Self::Integer32 => write!(f, "i32"),
            Self::Integer64 => write!(f, "i64"),
            Self::Float64 => write!(f, "f64"),
            Self::Float32 => write!(f, "f32"),
            Self::Pointer(t) => write!(f, "*{t:?}"),
            Self::Unsigned(t) => write!(f, "unsigned {t:?}"),
            Self::NullVoid => write!(f, "null"),
            Self::Boolean => write!(f, "bool"),
            Self::FatPointer(t, l) => write!(f, "*{l}[{T:?}]", T = t.deref()),
            Self::TerminatedSlice(t, term) => write!(f, "*:{term:?}[{T:?}]", T = t.deref()),
            Self::Aggregate(_, i) => write!(f, "aggregate {T:?}", T = i.deref()),
            Self::Generic(t, b) => write!(f, "generic {T:?}: {B:?}", T = t.deref(), B = b),
        }
    }
}

impl Display for QbeType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QbeType::Integer8 => write!(f, "c"),
            QbeType::Integer16 => write!(f, "s"),
            QbeType::Integer32 => write!(f, "i"),
            QbeType::Integer64 => write!(f, "l"),
            QbeType::Float64 => write!(f, "d"),
            QbeType::Float32 => write!(f, "f"),
            QbeType::Pointer(t) => write!(f, "P{t}"),
            QbeType::Unsigned(t) => write!(f, "U{t}"),
            QbeType::NullVoid => write!(f, "v"),
            QbeType::Boolean => write!(f, "b"),
            QbeType::FatPointer(t, l) => write!(f, "F{l}_{t}"),
            QbeType::TerminatedSlice(t, term) => write!(f, "E{term:?}_{t}"),
            QbeType::Aggregate(_, i) => write!(f, "{T}", T = i.deref()),
            QbeType::Generic(t, b) => write!(f, "G{T:?}:{B:?}", T = t.deref(), B = b),
        }
    }
}

impl<'a> FromStr for QbeType<'a> {
    type Err = QbeGenerationError<'a>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.chars().into_iter();

        Self::from_iter(&mut iter)
    }
}

impl<'a> QbeType<'a> {
    
    /// Returns true if a type can be iterated over in a 'for' loop.
    pub fn iterable(&self) -> bool {
        match self {
            QbeType::FatPointer(_, _) => true,
            QbeType::TerminatedSlice(_, _) => true,
            QbeType::Aggregate(_, i) => i.iterable(),
            _ => false
        }
    }

    /// A lossy conversion from a [QbeType] to a [qbe::Type],
    /// which cannot be reversed.
    pub fn into_qbe(self, use_sub: bool) -> qbe::Type<'a> {
        match self {
            QbeType::Integer8 | QbeType::NullVoid | QbeType::Boolean => if use_sub {
                qbe::Type::SignedByte
            } else {
                qbe::Type::Byte
            },
            QbeType::Integer16 => if use_sub {
                qbe::Type::SignedHalfword
            } else {
                qbe::Type::Halfword
            },
            QbeType::Integer32 => qbe::Type::Word,
            QbeType::Integer64 => qbe::Type::Long,
            QbeType::Pointer(_) => qbe::Type::Long,
            QbeType::Float64 => qbe::Type::Double,
            QbeType::Float32 => qbe::Type::Single,
            QbeType::Unsigned(t) => match t.deref().clone() {
                QbeType::Integer8 => if use_sub {
                    qbe::Type::UnsignedByte
                } else {
                    qbe::Type::Byte
                },
                QbeType::Integer16 => if use_sub {
                    qbe::Type::UnsignedHalfword
                } else {
                    qbe::Type::Halfword
                },
                t => t.into_qbe(use_sub),
            },
            QbeType::FatPointer(_, _) => qbe::Type::Long,
            QbeType::TerminatedSlice(_, _) => qbe::Type::Long,
            QbeType::Aggregate(_, i) => i.deref().clone().into_qbe(use_sub),
            QbeType::Generic(..) => unimplemented!("Type generics cannot be converted into QBE types."),
        }
    }
    
    pub fn size(&self) -> u64 {
        self.clone().into_qbe(false).size()
    }

    /// Equivalent to [QbeType::fmt], but fat pointers have their length erased.
    pub fn to_cmp_string(&self) -> String {
        match self {
            QbeType::FatPointer(t, _) => format!("F{t}"),
            _ => format!("{self}"),
        }
    }

    /// Equivalent to [QbeType::fmt], but "generics" are erased.
    pub fn to_type_erased_string(&self) -> String {
        match self {
            QbeType::FatPointer(_, _) => "F".to_string(),
            QbeType::TerminatedSlice(_, _) => "E".to_string(),
            QbeType::Pointer(_) => "P".to_string(),
            QbeType::Unsigned(_) => "U".to_string(),
            _ => format!("{self}"),
        }
    }

    pub fn into_qbe_abi(self) -> qbe::Type<'a> {
        self.into_qbe(false).into_abi()
    }
}

pub struct TypeGenerator;

impl<'a> TypeGenerator {
    pub fn new() -> Self {
        Self
    }

    pub fn generate_type(parse: ParseType, cg: &'a mut QbeGenerator<'a>, allowed_tgs: &HashMap<String, Option<TypeBound>>) -> QbeGenerationResult<'a, QbeType<'a>> {
        match parse {
            ParseType::IdentType(ref i) if allowed_tgs.contains_key(i) => Ok(QbeType::Generic(i.clone(), allowed_tgs.get(i).unwrap().clone())),
            ParseType::IdentType(ref i) => match cg.types().get(i) {
                Some(t) => Ok(t.clone()),
                None => Err(QbeGenerationError::UndefinedSymbol(i.clone())),
            },
            ParseType::ArrayType { .. } => todo!(),
            ParseType::PointerType(to) => Ok(QbeType::Pointer(Indirection::new(Self::generate_type(
                to.deref().clone(),
                cg,
                allowed_tgs,
            )?))),
            ParseType::FatPointerType(t, l) => Ok(QbeType::FatPointer(
                t.map_result(|p| Self::generate_type(p, cg, allowed_tgs))?,
                l,
            )),
            ParseType::TerminatedSlice(t, e) => Ok(QbeType::TerminatedSlice(
                t.map_result(|p| Self::generate_type(p, unsafe { (cg as *mut QbeGenerator<'a>).as_mut().unwrap() }, allowed_tgs))?,
                {
                    let expr = cg.generate_independent_expr(e.get());
                    Indirection::new(expr?)
                },
            )),
        }
    }
}
