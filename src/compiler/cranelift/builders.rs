use crate::compiler::cranelift::meta::VariableMeta;
use crate::compiler::cranelift::types::CraneliftType;
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::{FuncRef, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_codegen::isa::OwnedTargetIsa;
use cranelift_frontend::{FunctionBuilder, Variable};
use std::collections::HashMap;
use std::path::PathBuf;
use cranelift_codegen::ir::stackslot::StackSize;
use crate::compiler::cranelift::trace::Trace;

pub struct VariableBuilder {
    index: usize,
    scopes: Vec<HashMap<String, VariableMeta>>,
    pub(crate) flags: MemFlags,
    isa: OwnedTargetIsa,
}
impl VariableBuilder {
    pub(crate) fn new(isa: &OwnedTargetIsa) -> Self {
        Self {
            index: 0,
            scopes: vec![HashMap::new()],
            flags: MemFlags::trusted().with_checked(),
            isa: isa.clone(),
        }
    }

    pub fn create_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn create_var(
        &mut self,
        builder: &mut FunctionBuilder,
        value: Value,
        ty: CraneliftType,
        name: String,
        constant: bool,
    ) -> Variable {
        let variable = Variable::new(self.index);

        if constant {
            builder.declare_var(variable, ty.clone().into_cranelift(&self.isa));

            builder.def_var(variable, value);
        } else {
            builder.declare_var(variable, self.isa.pointer_type());
            
            let slot = builder.create_sized_stack_slot(StackSlotData {
                kind: StackSlotKind::ExplicitSlot,
                size: ty.size_bytes(&self.isa) as StackSize,
                align_shift: 0,
            });
            
            builder.ins().stack_store(value, slot, 0);
            
            let ptr = builder.ins().stack_addr(self.isa.pointer_type(), slot, 0);

            builder.def_var(variable, ptr);
        }

        self.scopes.last_mut().unwrap().insert(
            name.clone(),
            (self.index, variable, ty, constant).into(),
        );

        self.index += 1;

        variable
    }

    pub fn set_var(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &String,
        value: &Value,
        vty: &CraneliftType,
        file: PathBuf,
        trace: &Trace,
    ) -> Result<(), Box<[CompilationError]>> {
        let mut errors = vec![];

        let Some(scope) = self
            .scopes
            .iter()
            .filter(|vars| vars.contains_key(name))
            .last()
        else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        if meta.constant {
            errors.push(CompilationError::CannotMutate(
                file.clone(),
                trace.clone(),
                name.clone(),
            ));
        }

        if meta.def_type != *vty {
            errors.push(CompilationError::MismatchedTypeInDef(
                file,
                trace.clone(),
                name.clone(),
                meta.def_type.clone(),
                vty.clone(),
            ))
        }
        
        if !errors.is_empty() {
            return Err(errors.into());
        }

        let ptr = builder.use_var(meta.variable);

        builder.ins().store(self.flags, *value, ptr, 0);

        Ok(())
    }

    pub fn has_var(&self, name: &String) -> bool {
        self.scopes
            .iter()
            .filter(|vars| vars.contains_key(name))
            .collect::<Vec<_>>()
            .len()
            > 0
    }

    pub fn get_var(
        &self,
        builder: &mut FunctionBuilder,
        name: &String,
        file: PathBuf,
        trace: &Trace,
    ) -> Result<(Value, CraneliftType), Box<[CompilationError]>> {
        let Some(scope) = self
            .scopes
            .iter()
            .filter(|vars| vars.contains_key(name))
            .last()
        else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        let val = if meta.constant {
            builder.use_var(meta.variable)
        } else {
            let ptr = builder.use_var(meta.variable);
            builder.ins().load(
                meta.def_type.clone().into_cranelift(&self.isa),
                self.flags,
                ptr,
                0,
            )
        };

        Ok((val, meta.def_type.clone()))
    }

    pub fn get_var_ptr(
        &self,
        builder: &mut FunctionBuilder,
        name: &String,
        file: PathBuf,
        trace: &Trace,
    ) -> Result<(Value, CraneliftType), Box<[CompilationError]>> {
        let Some(scope) = self
            .scopes
            .iter()
            .filter(|vars| vars.contains_key(name))
            .last()
        else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                trace.clone(),
                name.clone(),
            )]));
        };

        let val = if meta.constant {
            return Err(Box::new([CompilationError::CannotMakePointer(
                file,
                trace.clone(),
                name.clone(),
            )]));
        } else {
            builder.use_var(meta.variable)
        };

        Ok((val, meta.def_type.clone()))
    }
}
