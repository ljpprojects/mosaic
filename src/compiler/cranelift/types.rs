#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use crate::compiler::cranelift::CraneliftGenerator;
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError;
use crate::parser::{AstNode, ParseType, TypeBound};
use crate::utils::Indirection;
use crate::utils::IndirectionTrait;
use cranelift_codegen::ir::{types, Type};
use cranelift_codegen::isa::OwnedTargetIsa;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum CraneliftType {
    Generic(String, Option<TypeBound>),
    Any,
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Float32,
    Float64,
    Null,
    Bool,
    FuncPtr {
        ret_type: Indirection<Self>,
        arg_types: Vec<Indirection<Self>>,
    },
    CPtr(Indirection<Self>),
    FatPtr(Indirection<Self>),
    Slice(Indirection<Self>, u32),

    // *:0[i8]
    CStr,

    // *:0[u8]
    UCStr,
}

impl PartialEq for CraneliftType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Any, _) => true,
            (Self::Int8, Self::Int8) => true,
            (Self::Int16, Self::Int16) => true,
            (Self::Int32, Self::Int32) => true,
            (Self::Int64, Self::Int64) => true,
            (Self::UInt8, Self::UInt8) => true,
            (Self::UInt16, Self::UInt16) => true,
            (Self::UInt32, Self::UInt32) => true,
            (Self::UInt64, Self::UInt64) => true,
            (Self::Bool, Self::Bool) => true,
            (Self::Null, Self::Null) => true,
            (Self::CPtr(ty), Self::CPtr(ty2)) => ty == ty2,
            (Self::FatPtr(ty), Self::FatPtr(ty2)) => ty == ty2,
            (Self::CPtr(ty), Self::UCStr) if ty.deref() == &Self::UInt8 => true,
            (Self::Float32, Self::Float32) => true,
            (Self::Float64, Self::Float64) => true,
            (
                Self::FuncPtr {
                    ret_type,
                    arg_types,
                },
                Self::FuncPtr {
                    ret_type: ret_type2,
                    arg_types: arg_types2,
                },
            ) => ret_type == ret_type2 && arg_types == arg_types2,
            (Self::Slice(ty, size), Self::Slice(ty2, size2)) => ty == ty2 && size == size2,
            _ => false,
        }
    }
}

impl CraneliftType {
    pub fn into_cranelift(self, isa: &OwnedTargetIsa) -> Type {
        match self {
            Self::Generic(name, _) => {
                panic!("The compiler has not evaluated the generic type '{name}'. This is a bug.")
            }
            Self::Any => panic!("Cannot use 'any' type unless it is behind a pointer."),
            Self::Int8 | Self::UInt8 => types::I8,
            Self::Int16 | Self::UInt16 => types::I16,
            Self::Int32 | Self::UInt32 => types::I32,
            Self::Int64 | Self::UInt64 => types::I64,
            Self::Float32 => types::F32,
            Self::Float64 => types::F64,
            Self::Null | Self::Bool => types::I8,
            Self::FuncPtr { .. } | Self::CPtr(_) | Self::Slice(..) | Self::CStr | Self::UCStr | Self::FatPtr(_) => {
                isa.pointer_type()
            }
        }
    }
}

impl Display for CraneliftType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CraneliftType::Generic(name, ..) => {
                panic!("The compiler has not evaluated the generic type '{name}'. This is a bug.")
            }
            CraneliftType::Any => write!(f, "any"),
            CraneliftType::Int8 => write!(f, "i8"),
            CraneliftType::Int16 => write!(f, "i16"),
            CraneliftType::Int32 => write!(f, "i32"),
            CraneliftType::Int64 => write!(f, "i64"),
            CraneliftType::UInt8 => write!(f, "u8"),
            CraneliftType::UInt16 => write!(f, "u16"),
            CraneliftType::UInt32 => write!(f, "u32"),
            CraneliftType::UInt64 => write!(f, "u64"),
            CraneliftType::Float32 => write!(f, "f32"),
            CraneliftType::Float64 => write!(f, "f64"),
            CraneliftType::Null => write!(f, "null"),
            CraneliftType::Bool => write!(f, "bool"),
            CraneliftType::FuncPtr { .. } => write!(f, "fn(...) -> ..."),
            CraneliftType::CPtr(i) => write!(f, "*{i}"),
            CraneliftType::FatPtr(i) => write!(f, "*[{i}]"),
            CraneliftType::Slice(i, l) => write!(f, "*{l}[{i}]"),
            CraneliftType::CStr => write!(f, "*:0[i8]"),
            CraneliftType::UCStr => write!(f, "*:0[u8]"),
        }
    }
}

impl CompilationType for CraneliftType {
    fn is_numeric(&self) -> bool {
        matches!(self, Self::Int8
            | Self::Int16
            | Self::Int32
            | Self::Int64
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::UInt64
            | Self::Float32
            | Self::Float64)
    }

    fn to_unsigned(&self) -> Option<Self> {
        match self {
            Self::Int8 => Some(Self::Int8),
            Self::Int16 => Some(Self::Int16),
            Self::Int32 => Some(Self::Int32),
            Self::Int64 => Some(Self::Int64),
            _ => None,
        }
    }

    fn is_signed(&self) -> bool {
        matches!(self, Self::Int8
            | Self::Int16
            | Self::Int32
            | Self::Int64
            | Self::Float32
            | Self::Float64)
    }

    fn is_pointer(&self) -> bool {
        matches!(self, Self::CPtr(_) | Self::FuncPtr { .. } | Self::CStr | Self::Slice(..) | Self::UCStr | Self::FatPtr(_))
    }

    fn is_c_abi(&self) -> bool {
        matches!(self, Self::Float32 | Self::Float64 | Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64 | Self::UInt8 | Self::UInt16 | Self::UInt32 | Self::UInt64 | Self::CPtr(_) | Self::CStr | Self::UCStr | Self::FuncPtr { .. })
    }

    fn into_c_abi(self) -> Self {
        match self {
            Self::Bool | Self::Null => Self::Int8,
            Self::Slice(inner, _) => Self::CPtr(inner),
            ty => ty,
        }
    }

    fn size_bytes(&self, isa: &OwnedTargetIsa) -> u8 {
        match self {
            Self::Generic(name, ..) => {
                panic!("The compiler has not evaluated the generic type '{name}'. This is a bug.")
            }
            Self::Any => panic!("Cannot get size of type 'any'."),
            Self::Int8 | Self::UInt8 => 1,
            Self::Int16 | Self::UInt16 => 2,
            Self::Int32 | Self::UInt32 => 4,
            Self::Int64 | Self::UInt64 => 8,
            Self::Float32 => 4,
            Self::Float64 => 8,
            Self::Null | Self::Bool => 1,
            Self::FuncPtr { .. } | Self::CPtr(_) | Self::Slice(..) | Self::CStr | Self::UCStr | Self::FatPtr(_) => {
                isa.pointer_bytes()
            }
        }
    }

    fn size_bits(&self, isa: &OwnedTargetIsa) -> u8 {
        self.size_bytes(isa) * 8
    }

    fn inner(&self) -> Option<Self> {
        match self {
            CraneliftType::CPtr(i) => Some(i.deref().clone()),
            CraneliftType::Slice(i, _) => Some(i.deref().clone()),
            CraneliftType::CStr => Some(Self::Int8),
            CraneliftType::UCStr => Some(Self::UInt8),
            CraneliftType::FatPtr(i) => Some(i.deref().clone()),
            _ => None,
        }
    }

    /// Returns Some(alias) if Cranelift doesn't support a direct mapping of this type.
    fn pseudo(&self) -> Option<Self> {
        match self {
            Self::Bool | Self::Null => Some(Self::Int8),
            _ => None,
        }
    }

    fn cmp_eq(&self, other: &CraneliftType) -> bool {
        (self.is_numeric() && other.is_numeric())
            || (self.is_pointer() && other.is_pointer())
            || (self == other)
    }

    fn iterable(&self) -> bool {
        matches!(self, Self::Slice(..) | Self::CStr | Self::UCStr | Self::FatPtr(..))
    }
    
    fn matches_bound(
        &self,
        bound: TypeBound,
        gen: &CraneliftGenerator,
        allowed_tgs: &HashMap<String, Option<TypeBound>>,
    ) -> Result<bool, Box<[CompilationError]>> {
        match bound {
            TypeBound::Iterator(ref ty) => {
                if !self.iterable() {
                    return Ok(false);
                }
                
                match self {
                    Self::Slice(t, ..) => {
                        Ok(t.deref().clone() == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs))
                    }
                    Self::CStr => {
                        Ok(Self::Int8 == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs))
                    }
                    Self::UCStr => {
                        Ok(Self::UInt8 == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs))
                    }
                    
                    Self::FatPtr(_) => {
                        Ok(Self::UInt8 == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs))
                    }
                    _ => Ok(false),
                }
            },
            TypeBound::Not(t) => self
                .matches_bound(t.deref().clone(), gen, allowed_tgs)
                .map(|b| !b),
            TypeBound::Compound(bounds) => {
                for bound in bounds {
                    let matches = self.matches_bound(bound, gen, allowed_tgs)?;
                    if !matches {
                        return Ok(false);
                    }
                }

                Ok(true)
            }
        }
    }
}

pub struct TypeGenerator {
    types: HashMap<String, CraneliftType>,
}

impl Default for TypeGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeGenerator {
    pub fn new() -> Self {
        Self {
            types: HashMap::from([
                ("i8".into(), CraneliftType::Int8),
                ("i16".into(), CraneliftType::Int16),
                ("i32".into(), CraneliftType::Int32),
                ("i64".into(), CraneliftType::Int64),
                ("u8".into(), CraneliftType::UInt8),
                ("u16".into(), CraneliftType::UInt16),
                ("u32".into(), CraneliftType::UInt32),
                ("u64".into(), CraneliftType::UInt64),
                ("null".into(), CraneliftType::Null),
                ("bool".into(), CraneliftType::Bool),
                ("any".into(), CraneliftType::Any),
                ("f32".into(), CraneliftType::Float32),
                ("f64".into(), CraneliftType::Float64),
            ]),
        }
    }

    pub fn merge(&mut self, other: &Self) {
        self.types.extend(other.types.clone());
    }

    pub fn register_type(&mut self, name: String, ty: CraneliftType) {
        self.types.insert(name, ty);
    }

    pub fn get_type(&self, name: &String) -> CraneliftType {
        self.types
            .get(name)
            .expect(&*format!("Unknown type '{name}'"))
            .clone()
    }

    pub fn compile_type_no_tgs(&self, ty: &ParseType, isa: &OwnedTargetIsa) -> CraneliftType {
        match ty {
            ParseType::IdentType(i) => self
                .types
                .get(i)
                .expect(&*format!("Unknown type '{i}'"))
                .clone(),
            ParseType::ArrayType { .. } => {
                panic!("Array types are obsolete; use slice types instead.")
            }
            ParseType::PointerType(i) => CraneliftType::CPtr(
                i.clone()
                    .map(|t| self.compile_type(&t, isa, &HashMap::default())),
            ),
            ParseType::FatPointerType(i) => CraneliftType::FatPtr(
                i.clone()
                    .map(|t| self.compile_type(&t, isa, &HashMap::default())),
            ),
            ParseType::Slice(i, l) => CraneliftType::Slice(
                i.clone()
                    .map(|t| self.compile_type(&t, isa, &HashMap::default())),
                *l,
            ),
            ParseType::TerminatedSlice(i, t) => {
                assert!(matches!(t.deref(), AstNode::NumberLiteral(_)));

                if let AstNode::NumberLiteral(n) = t.deref() {
                    if *n != 0f64 {
                        panic!("Only null-terminated slices are supported.")
                    }
                };

                let ty = i
                    .clone()
                    .map(|t| self.compile_type(t, isa, &HashMap::default()));

                match ty.deref() {
                    CraneliftType::Int8 => CraneliftType::CStr,
                    CraneliftType::UInt8 => CraneliftType::UCStr,
                    _ => panic!("Only i8 & u8 terminated slices (c strings) are supported."),
                }
            }
            ParseType::FuncPtr(args, ret) => {
                let args = args
                    .iter()
                    .map(|t| Indirection::new(self.compile_type(t, isa, &HashMap::default())))
                    .collect::<Vec<_>>();
                let ret = self.compile_type(ret, isa, &HashMap::default());

                CraneliftType::FuncPtr {
                    ret_type: Rc::new(ret),
                    arg_types: args,
                }
            }
        }
    }

    pub fn compile_type(
        &self,
        ty: &ParseType,
        isa: &OwnedTargetIsa,
        tgs: &HashMap<String, Option<TypeBound>>,
    ) -> CraneliftType {
        match ty {
            ParseType::IdentType(i) if tgs.contains_key(i) => {
                CraneliftType::Generic(i.clone(), tgs.get(i).unwrap().clone())
            }
            ParseType::IdentType(i) => self
                .types
                .get(i)
                .expect(&*format!("Unknown type '{i}'"))
                .clone(),
            ParseType::ArrayType { .. } => {
                panic!("Array types are obsolete; use slice types instead.")
            }
            ParseType::PointerType(i) => {
                CraneliftType::CPtr(i.clone().map(|t| self.compile_type(&t, isa, tgs)))
            }
            ParseType::FatPointerType(i) => CraneliftType::FatPtr(
                i.clone()
                    .map(|t| self.compile_type(&t, isa, &HashMap::default())),
            ),
            ParseType::Slice(i, l) => CraneliftType::Slice(
                i.clone().map(|t| self.compile_type(&t, isa, tgs)),
                *l,
            ),
            ParseType::TerminatedSlice(i, t) => {
                assert!(matches!(t.deref(), AstNode::NumberLiteral(_)));

                if let AstNode::NumberLiteral(n) = t.deref() {
                    if *n != 0f64 {
                        panic!("Only null-terminated slices are supported.")
                    }
                };

                let ty = i.clone().map(|t| self.compile_type(t, isa, tgs));

                match ty.deref() {
                    CraneliftType::Int8 => CraneliftType::CStr,
                    CraneliftType::UInt8 => CraneliftType::UCStr,
                    _ => panic!("Only i8 & u8 terminated slices (c strings) are supported."),
                }
            }
            ParseType::FuncPtr(args, ret) => {
                let args = args
                    .iter()
                    .map(|t| Indirection::new(self.compile_type(t, isa, tgs)))
                    .collect::<Vec<_>>();
                let ret = self.compile_type(ret, isa, tgs);

                CraneliftType::FuncPtr {
                    ret_type: Rc::new(ret),
                    arg_types: args,
                }
            }
        }
    }
}
