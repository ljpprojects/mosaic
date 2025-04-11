#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use crate::compiler::cranelift::CraneliftGenerator;
use crate::compiler::traits;
use crate::compiler::traits::TypeGenerator as OtherTypeGenerator;
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
    CPtr(Indirection<Self>, bool, bool),
    FatPtr(Indirection<Self>, bool, bool),
    Slice(Indirection<Self>, u32, bool, bool),
    
    /// Stores the name of the data declaration the value conforms to.
    /// Mutability is enforced on a per-field basis.
    /// Nullability is achieved by using a wrapper.
    DataPtr(String),
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
            (Self::CPtr(ty, ..), Self::CPtr(ty2, ..)) => ty == ty2,
            (Self::FatPtr(ty, ..), Self::FatPtr(ty2, ..)) => ty == ty2,
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
            (Self::Slice(ty, size, ..), Self::Slice(ty2, size2, ..)) => ty == ty2 && size == size2,
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
            Self::DataPtr(..) | Self::FuncPtr { .. } | Self::CPtr(..) | Self::Slice(..) | Self::FatPtr(..) => {
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
            CraneliftType::DataPtr(name) => write!(f, "data {}", name),
            CraneliftType::FuncPtr { .. } => write!(f, "fn(...) -> ..."),
            CraneliftType::CPtr(i, mutable, nullable) => write!(f, "*{}{} {i}", if *mutable { "mut" } else { "const" }, if *nullable { "?" } else { "" }),
            CraneliftType::FatPtr(i, mutable, nullable) => write!(f, "*{}{} [{i}]", if *mutable { "mut" } else { "const" }, if *nullable { "?" } else { "" }),
            CraneliftType::Slice(i, l, mutable, nullable) => write!(f, "*{}{} {l}[{i}]", if *mutable { "mut" } else { "const" }, if *nullable { "?" } else { "" }),
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

    fn is_pointer(&self) -> bool {
        matches!(self, Self::CPtr(..) | Self::FuncPtr { .. } | Self::Slice(..) | Self::FatPtr(..))
    }

    fn is_c_abi(&self) -> bool {
        matches!(self, Self::Float32 | Self::Float64 | Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64 | Self::UInt8 | Self::UInt16 | Self::UInt32 | Self::UInt64 | Self::CPtr(..) | Self::FuncPtr { .. })
    }

    fn is_signed(&self) -> bool {
        matches!(self, Self::Int8
            | Self::Int16
            | Self::Int32
            | Self::Int64
            | Self::Float32
            | Self::Float64)
    }

    fn into_c_abi(self) -> Rc<dyn CompilationType> {
        match self {
            Self::Bool | Self::Null => Rc::new(Self::Int8),
            Self::Slice(inner, _, mutable, nullable) => Rc::new(Self::CPtr(inner, mutable, nullable)),
            ty => Rc::new(ty),
        }
    }

    fn to_unsigned(&self) -> Option<Rc<dyn CompilationType>> {
        match self {
            Self::Int8 => Some(Rc::new(Self::Int8)),
            Self::Int16 => Some(Rc::new(Self::Int16)),
            Self::Int32 => Some(Rc::new(Self::Int32)),
            Self::Int64 => Some(Rc::new(Self::Int64)),
            _ => None,
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
            Self::DataPtr(..) | Self::FuncPtr { .. } | Self::CPtr(..) | Self::Slice(..) | Self::FatPtr(..) => {
                isa.pointer_bytes()
            }
        }
    }

    fn size_bits(&self, isa: &OwnedTargetIsa) -> u8 {
        self.size_bytes(isa) * 8
    }

    fn inner(&self) -> Option<Rc<dyn CompilationType>> {
        match self {
            CraneliftType::CPtr(i, ..) => Some(Rc::new(i.deref().clone())),
            CraneliftType::Slice(i, ..) => Some(Rc::new(i.deref().clone())),
            CraneliftType::FatPtr(i, ..) => Some(Rc::new(i.deref().clone())),
            _ => None,
        }
    }

    /// Returns Some(alias) if Cranelift doesn't support a direct mapping of this type.
    fn pseudo(&self) -> Option<Rc<dyn CompilationType>> {
        match self {
            Self::Bool | Self::Null => Some(Rc::new(Self::Int8)),
            _ => None,
        }
    }

    fn cmp_eq(&self, other: Rc<dyn CompilationType>) -> bool {
        let other = other.downcast_ref::<Self>().unwrap();
        
        (self.is_numeric() && other.is_numeric())
            || (self.is_pointer() && other.is_pointer())
            || (self == other)
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
                        Ok(t.deref().clone() == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs).downcast_ref::<CraneliftType>().unwrap().clone())
                    }
                    
                    Self::FatPtr(..) => {
                        Ok(Self::UInt8 == gen.tg.compile_type(ty.deref(), &gen.isa, allowed_tgs).downcast_ref::<CraneliftType>().unwrap().clone())
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

    fn iterable(&self) -> bool {
        matches!(self, Self::Slice(..) | Self::FatPtr(..))
    }
}

pub struct CraneliftTypeGenerator {
    types: HashMap<String, CraneliftType>,
}

impl CraneliftTypeGenerator {
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
}

impl Default for CraneliftTypeGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl traits::TypeGenerator for CraneliftTypeGenerator {
    fn types(&self) -> HashMap<String, Box<dyn CompilationType>> {
        self.types.iter().map(|(k, v)| (k.clone(), Box::new(v.clone()) as Box<dyn CompilationType>)).collect()
    }
    
    fn merge(&mut self, other: &dyn traits::TypeGenerator) {
        self.types.extend(other.types().iter().map(|(k, v)| (k.clone(), v.downcast_ref::<CraneliftType>().unwrap().clone())).collect::<HashMap<_, _>>());
    }

    fn register_type(&mut self, name: &String, ty: Box<dyn CompilationType>) {
        self.types.insert(name.clone(), ty.downcast_ref::<CraneliftType>().unwrap().clone());
    }

    fn get_type(&self, name: &String) -> Box<dyn CompilationType> {
        Box::new(self.types
            .get(name)
            .expect(&*format!("Unknown type '{name}'"))
            .clone())
    }

    fn compile_type_no_tgs(&self, ty: &ParseType, isa: &OwnedTargetIsa) -> Box<dyn CompilationType> {
        self.compile_type(ty, isa, &HashMap::default())
    }

    fn compile_type(
        &self,
        ty: &ParseType,
        isa: &OwnedTargetIsa,
        tgs: &HashMap<String, Option<TypeBound>>,
    ) -> Box<dyn CompilationType> {
        Box::new(match ty {
            ParseType::IdentType(i) if tgs.contains_key(i) => {
                CraneliftType::Generic(i.clone(), tgs.get(i).unwrap().clone())
            }
            ParseType::IdentType(i) => self
                .types
                .get(i)
                .expect(&*format!("Unknown type '{i}'"))
                .clone(),
            ParseType::PointerType {
                points_to,
                is_nullable,
                is_mutable,
            } => {
                CraneliftType::CPtr(points_to.clone().map(|t| self.compile_type(&t, isa, tgs).downcast_ref::<CraneliftType>().unwrap().clone()), *is_mutable, *is_nullable)
            }
            ParseType::FatPointerType {
                points_to,
                is_nullable,
                is_mutable,
            } => CraneliftType::FatPtr(
                points_to.clone()
                    .map(|t| self.compile_type(&t, isa, &HashMap::default()).downcast_ref::<CraneliftType>().unwrap().clone()),
                *is_mutable,
                *is_nullable,
            ),
            ParseType::Slice{
                points_to,
                is_nullable,
                is_mutable,
                length
            } => CraneliftType::Slice(
                points_to.clone().map(|t| self.compile_type(&t, isa, tgs).downcast_ref::<CraneliftType>().unwrap().clone()),
                *length,
                *is_mutable,
                *is_nullable,
            ),
            ParseType::FuncPtr(args, ret) => {
                let args = args
                    .iter()
                    .map(|t| self.compile_type(t, isa, tgs))
                    .collect::<Vec<_>>();
                let ret = self.compile_type(ret, isa, tgs);

                CraneliftType::FuncPtr {
                    ret_type: Indirection::new(ret.downcast_ref::<CraneliftType>().unwrap().clone()),
                    arg_types: args.iter().map(|a| Indirection::new(a.downcast_ref::<CraneliftType>().unwrap().clone())).collect(),
                }
            }
        })
    }
}