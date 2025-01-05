use crate::compiler::cranelift::types::CraneliftType;
use crate::parser::Modifier;
use cranelift_codegen::ir::{Block, Signature, Value};
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
    pub methods: HashMap<String, Vec<FunctionMeta>>
}

#[derive(Clone, Debug)]
pub struct FieldMeta {
    offset: usize,
    field_type: CraneliftType,
    modifiers: Box<[Modifier]>,
    default: Option<Value>,
}