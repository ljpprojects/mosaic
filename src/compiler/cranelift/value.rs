use crate::utils::Indirection;
use cranelift_codegen::ir::Value as RawValue;

pub enum CraneliftValue {
    SignedInteger(i64),
    UnsignedInteger(u64),
    Bool(bool),
    Null,
    Pointer(RawValue, Option<Indirection<CraneliftValue>>),
    Float(f64),
}

impl CraneliftValue {}
