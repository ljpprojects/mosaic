use std::rc::Rc;
use crate::compiler::cranelift::types::CraneliftType;
use crate::parser::Modifier;
use cranelift_codegen::ir::{Block, Signature, Value};
use cranelift_frontend::Variable;
use crate::compiler::traits::CompilationType;

#[derive(Clone)]
pub struct FunctionMeta {
    pub auto_free_idx: Option<usize>,
    pub modifiers: Box<[Modifier]>,
    pub arity: usize,
    pub arg_meta: Vec<(String, Rc<dyn CompilationType>)>,
    pub return_type: Rc<dyn CompilationType>,
    pub sig: Signature,
    pub index: u32,
    pub start_block: Option<Block>,
}

#[derive(Clone)]
pub struct DataDeclMeta {
    pub size: u16,
    pub alignment: u8,
    pub fields: Vec<(u16, bool, String, Rc<dyn CompilationType>)>, // offset, is_mutable, name, type
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
