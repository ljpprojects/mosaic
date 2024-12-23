use crate::utils::IndirectionTrait;
use std::collections::HashMap;
use std::ops::Deref;
use cranelift_codegen::ir::{types, Type};
use cranelift_codegen::isa::OwnedTargetIsa;
use crate::parser::{AstNode, ParseType};
use crate::utils::Indirection;

#[derive(Clone, Debug, PartialEq)]
pub enum CraneliftType {
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
    Slice(Indirection<Self>, usize),
    
    // *:0[i8]
    CStr,
    
    // *:0[u8]
    UCStr,
}

impl CraneliftType {
    pub fn is_numeric(&self) -> bool {
        match self {
            Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64 | Self::UInt8 | Self::UInt16 | Self::UInt32 | Self::UInt64 | Self::Float32 | Self::Float64 => true,
            _ => false,
        }
    }
    
    pub fn is_pointer(&self) -> bool {
        match self {
            Self::CPtr(_) | Self::FuncPtr { .. } | Self::CStr | Self::Slice(..) | Self::UCStr => true,
            _ => false,
        }
    }
    
    pub fn is_c_abi(&self) -> bool {
        match self {
            Self::Float32 | Self::Float64 => true,
            Self::Int8    | Self::Int16  | Self::Int32  | Self::Int64 => true,
            Self::UInt8   | Self::UInt16 | Self::UInt32 | Self::UInt64 => true,
            Self::CPtr(_) | Self::CStr   | Self::UCStr  | Self::FuncPtr { .. } => true,
            _ => false,
        }
    }

    pub fn into_c_abi(self) -> Self {
        match self {
            Self::Bool | Self::Null => Self::Int8,
            Self::Slice(inner, _) => Self::CPtr(inner),
            ty => ty
        }
    }
    
    pub fn into_cranelift(self, isa: &OwnedTargetIsa) -> Type {
        match self {
            Self::Int8 | Self::UInt8 => types::I8,
            Self::Int16 | Self::UInt16 => types::I16,
            Self::Int32 | Self::UInt32 => types::I32,
            Self::Int64 | Self::UInt64 => types::I64,
            Self::Float32 => types::F32,
            Self::Float64 => types::F64,
            Self::Null | Self::Bool => types::I8,
            Self::FuncPtr { .. } | Self::CPtr(_) | Self::Slice(_, _) | Self::CStr | Self::UCStr => isa.pointer_type()
        }
    }
    
    pub fn size_bytes(&self, isa: &OwnedTargetIsa) -> u8 {
        match self {
            Self::Int8 | Self::UInt8 => 1,
            Self::Int16 | Self::UInt16 => 2,
            Self::Int32 | Self::UInt32 => 4,
            Self::Int64 | Self::UInt64 => 8,
            Self::Float32 => 4,
            Self::Float64 => 8,
            Self::Null | Self::Bool => 1,
            Self::FuncPtr { .. } | Self::CPtr(_) | Self::Slice(_, _) | Self::CStr | Self::UCStr => isa.pointer_bytes(),
        }
    }

    pub fn size_bits(&self, isa: &OwnedTargetIsa) -> u8 {
        self.size_bytes(isa) * 8
    }
    
    pub fn inner(&self) -> Option<Self> {
        match self {
            CraneliftType::CPtr(i) => Some(i.deref().clone()),
            CraneliftType::Slice(i, _) => Some(i.deref().clone()),
            CraneliftType::CStr => Some(Self::Int8),
            CraneliftType::UCStr => Some(Self::UInt8),
             _ => None
        }
    }
    
    /// Returns Some(alias) if Cranelift doesn't support a direct mapping of this type.
    pub fn is_pseudo(&self) -> Option<Self> {
        match self {
            Self::Bool | Self::Null => Some(Self::Int8),
            _ => None
        }
    }
}

pub struct TypeGenerator {
    types: HashMap<String, CraneliftType>,
}

impl TypeGenerator {
    pub fn new() -> Self {
        Self {
            types: HashMap::from([
                ("i8".into(), CraneliftType::Int8),
                ("i16".into(), CraneliftType::Int16),
                ("i32".into(), CraneliftType::Int32),
                ("i64".into(), CraneliftType::Int64),
                ("i8".into(), CraneliftType::UInt8),
                ("i16".into(), CraneliftType::UInt16),
                ("i32".into(), CraneliftType::UInt32),
                ("i64".into(), CraneliftType::UInt64),
                ("null".into(), CraneliftType::Null),
            ]),
        }
    }
    
    pub fn merge(&mut self, other: &Self) {
        self.types.extend(other.types.clone());
    }

    pub fn register_type(&mut self, name: String, ty: CraneliftType) {
        self.types.insert(name, ty);
    }

    pub fn compile_type(&self, ty: &ParseType, isa: &OwnedTargetIsa) -> CraneliftType {
        match ty {
            ParseType::IdentType(i) => self.types.get(i).expect(&*format!("Unknown type '{i}'")).clone(),
            ParseType::ArrayType { .. } => panic!("Array types are obsolete; use slice types instead."),
            ParseType::PointerType(i) => CraneliftType::CPtr(i.clone().map(|t| self.compile_type(&t, isa))),
            ParseType::FatPointerType(i, l) => CraneliftType::Slice(i.clone().map(|t| self.compile_type(&t, isa)), *l as usize),
            ParseType::TerminatedSlice(i, t) => {
                assert!(matches!(t.deref(), AstNode::NumberLiteral(_)));

                if let AstNode::NumberLiteral(n) = t.deref() && *n != 0f64 {
                    panic!("Only null-terminated slices are supported.")
                };

                let ty = i.clone().map(|t| self.compile_type(t, isa));

                match ty.deref() {
                    CraneliftType::Int8 => CraneliftType::CStr,
                    CraneliftType::UInt8 => CraneliftType::UCStr,
                    _ => panic!("Only i8 & u8 terminated slices (c strings) are supported.")
                }
            },
        }
    }
}