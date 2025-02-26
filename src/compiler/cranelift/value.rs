use crate::utils::{Indirection, OneOf};
use cranelift_codegen::ir::{self, InstBuilder, StackSlot, StackSlotData, StackSlotKind, Value as RawValue};
use cranelift_frontend::FunctionBuilder;
use crate::compiler::identifiers::StatementIdentifier;

pub struct OwnershipTrace {
    /// Stores the name of the variable that owns the value, if any
    owner: OneOf<String, String, StatementIdentifier>,
}

pub struct MethodTableValue {
    mangled_method_names: Vec<String>,
    implements: Vec<String>
}

impl MethodTableValue {
    pub fn new(mangled_method_names: Vec<String>, implements: Vec<String>) -> Self {
        Self {
            mangled_method_names,
            implements
        }
    }

    pub fn into_stackslot(self, func: &mut FunctionBuilder) -> StackSlot {
        let size = 4 + self.mangled_method_names.iter().map(|name| 2 + name.len() as u32).sum::<u32>() + 4 + self.implements.iter().map(|name| 2 + name.len() as u32).sum::<u32>();

        let data = StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size,
            0 // let cranelift do this work
        );

        let slot = func.create_sized_stack_slot(data);

        let mangled_methods_len = func.ins().iconst(ir::types::I32, self.mangled_method_names.len() as i64);

        func.ins().stack_store(mangled_methods_len, slot, 0);

        slot
    }
}

pub enum CraneliftValue {
    Integer(i64, u8, OwnershipTrace),
    UnsignedInetger(u64, u8, OwnershipTrace),
    Float(f64, u8, OwnershipTrace),
    Null(OwnershipTrace),
    Boolean(bool, OwnershipTrace),
    CPtr(RawValue, OwnershipTrace),
    Slice(RawValue, OwnershipTrace),
    CString(OwnershipTrace),
    UnsignedCString(OwnershipTrace),
    FunctionPtr(RawValue, OwnershipTrace),
    Reference(RawValue, OwnershipTrace, bool),
    SomeObjectReference(MethodTableValue, OwnershipTrace, bool)
}

impl CraneliftValue {}
