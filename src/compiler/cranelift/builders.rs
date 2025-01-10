use crate::compiler::cranelift::types::CraneliftType;
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::{FuncRef, InstBuilder, MemFlags, Value};
use cranelift_codegen::isa::OwnedTargetIsa;
use cranelift_frontend::{FunctionBuilder, Variable};
use std::collections::HashMap;
use std::path::PathBuf;
use crate::compiler::cranelift::meta::VariableMeta;

pub struct VariableBuilder {
    index: usize,
    scopes: Vec<HashMap<String, VariableMeta>>,
    flags: MemFlags,
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

    pub fn create_scope(
        &mut self,
    ) {
        self.scopes.push(HashMap::new());
    }

    pub fn create_var(
        &mut self,
        builder: &mut FunctionBuilder,
        value: Value,
        ty: CraneliftType,
        name: String,
        constant: bool,
        alloc_fn: FuncRef,
    ) -> Variable {
        let variable = Variable::new(self.index);

        if constant {
            builder.declare_var(variable, ty.clone().into_cranelift(&self.isa));
            
            builder.def_var(variable, value);
        } else {
            builder.declare_var(variable, self.isa.pointer_type());

            let size = builder.ins().iconst(
                CraneliftType::Int32.into_cranelift(&self.isa),
                ty.size_bytes(&self.isa) as i64,
            );

            let ptr = builder.ins().call(alloc_fn, &[size]);
            let ptr = builder.inst_results(ptr)[0];

            builder.ins().store(self.flags, value, ptr, 0);

            builder.def_var(variable, ptr);
        }

        self.scopes.last_mut().unwrap().insert(name.clone(), (value, self.index, variable, ty, constant).into());

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
    ) -> Result<(), Box<[CompilationError]>> {
        let mut errors = vec![];

        let Some(scope) = self.scopes.iter().filter(|vars| vars.contains_key(name)).last() else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        if meta.constant {
            return Err(Box::new([CompilationError::CannotMutate(file, name.clone())]));
        }

        if meta.def_type != *vty {
            errors.push(CompilationError::MismatchedTypeInDef(
                file,
                name.clone(),
                meta.def_type.clone(),
                vty.clone(),
            ))
        }

        let ptr = builder.use_var(meta.variable);

        builder.ins().store(self.flags, *value, ptr, 0);

        Ok(())
    }

    pub fn has_var(
        &self,
        name: &String,
    ) -> bool {
        self.scopes.iter().filter(|vars| vars.contains_key(name)).collect::<Vec<_>>().len() > 0
    }

    pub fn get_var(
        &self,
        builder: &mut FunctionBuilder,
        name: &String,
        file: PathBuf,
    ) -> Result<(Value, CraneliftType), Box<[CompilationError]>> {
        let Some(scope) = self.scopes.iter().filter(|vars| vars.contains_key(name)).last() else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let val = if meta.constant {
            // since the value of a constant cannot change,
            // the last assigned value is the current value.
            meta.last_assigned
        } else {
            let ptr = builder.use_var(meta.variable);
            builder
                .ins()
                .load(meta.def_type.clone().into_cranelift(&self.isa), self.flags, ptr, 0)
        };

        Ok((val, meta.def_type.clone()))
    }

    pub fn get_var_ptr(
        &self,
        builder: &mut FunctionBuilder,
        name: &String,
        file: PathBuf,
    ) -> Result<(Value, CraneliftType), Box<[CompilationError]>> {
        let Some(scope) = self.scopes.iter().filter(|vars| vars.contains_key(name)).last() else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let Some(meta) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let val = if meta.constant {
            return Err(Box::new([CompilationError::CannotMakePointer(file, name.clone())]));
        } else {
            let ptr = builder.use_var(meta.variable);
            builder
                .ins()
                .load(meta.def_type.clone().into_cranelift(&self.isa), self.flags, ptr, 0)
        };

        Ok((val, meta.def_type.clone()))
    }
}
