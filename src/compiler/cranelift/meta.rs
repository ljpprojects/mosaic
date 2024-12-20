use cranelift_codegen::ir::{Block, Signature};
use crate::parser::Modifier;

#[derive(Clone, Debug)]
pub struct FunctionMeta {
    pub(crate) auto_free_idx: Option<usize>,
    pub(crate) modifiers: Box<[Modifier]>,
    pub(crate) arity: usize,
    pub(crate) arg_meta: Vec<(String, crate::compiler::cranelift::types::CraneliftType)>,
    pub(crate) return_type: crate::compiler::cranelift::types::CraneliftType,
    pub(crate) sig: Signature,
    pub(crate) index: u32,
    pub(crate) start_block: Option<Block>,
}