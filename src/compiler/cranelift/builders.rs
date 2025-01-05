use crate::compiler::cranelift::types::CraneliftType;
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::{FuncRef, InstBuilder, MemFlags, Value};
use cranelift_codegen::isa::OwnedTargetIsa;
use cranelift_frontend::{FunctionBuilder, Variable};
use std::collections::HashMap;
use std::path::PathBuf;

pub struct VariableBuilder {
    index: usize,
    scopes: Vec<HashMap<String, (usize, Variable, CraneliftType, bool)>>,
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

        self.scopes.last_mut().unwrap().insert(name.clone(), (self.index, variable, ty, constant));

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

        let Some((_, variable, ty, constant)) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        if *constant {
            return Err(Box::new([CompilationError::CannotMutate(file, name.clone())]));
        }

        if ty != vty {
            errors.push(CompilationError::MismatchedTypeInDef(
                file,
                name.clone(),
                ty.clone(),
                vty.clone(),
            ))
        }

        let ptr = builder.use_var(*variable);

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

        let Some((_, variable, ty, constant)) = scope.get(name) else {
            return Err(Box::new([CompilationError::UndefinedVariable(
                file,
                name.clone(),
            )]));
        };

        let val = if *constant {
            builder.use_var(*variable)
        } else {
            let ptr = builder.use_var(*variable);
            builder
                .ins()
                .load(ty.clone().into_cranelift(&self.isa), self.flags, ptr, 0)
        };

        Ok((val, ty.clone()))
    }
}
