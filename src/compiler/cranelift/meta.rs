use crate::compiler::cranelift::types::CraneliftType;
use crate::parser::Modifier;
use cranelift_codegen::ir::{Block, Signature, Value};
use cranelift_frontend::Variable;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct FunctionMeta {
    pub auto_free_idx: Option<usize>,
    pub modifiers: Box<[Modifier]>,
    pub arity: usize,
    pub arg_meta: Vec<(String, CraneliftType)>,
    pub return_type: CraneliftType,
    pub sig: Signature,
    pub index: u32,
    pub start_block: Option<Block>,
}

#[derive(Clone, Debug)]
pub struct StructMeta {
    pub fields: HashMap<String, FieldMeta>,
    pub methods: HashMap<String, Vec<FunctionMeta>>,
}

#[derive(Clone, Debug)]
pub struct FieldMeta {
    offset: usize,
    field_type: CraneliftType,
    modifiers: Box<[Modifier]>,
    default: Option<Value>,
}

#[derive(Hash, Clone, Debug, PartialEq, Eq)]
pub struct MustFreeMeta {
    pub(crate) value: Value,
    pub(crate) returned_from: String,
}

impl From<(Value, String)> for MustFreeMeta {
    fn from(value: (Value, String)) -> MustFreeMeta {
        Self {
            value: value.0,
            returned_from: value.1,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct VariableMeta {
    pub constant: bool,
    pub variable: Variable,
    pub index: usize,
    pub def_type: CraneliftType,
}

impl From<(usize, Variable, CraneliftType, bool)> for VariableMeta {
    fn from(value: (usize, Variable, CraneliftType, bool)) -> Self {
        Self {
            constant: value.3,
            variable: value.1,
            index: value.0,
            def_type: value.2,
        }
    }
}
