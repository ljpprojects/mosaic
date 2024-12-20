use std::collections::HashMap;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir;
use cranelift_codegen::ir::Value;
use cranelift_frontend::{FunctionBuilder, Variable};

pub struct VariableBuilder {
    index: usize,
    variables: HashMap<String, (usize, Variable, crate::compiler::cranelift::types::CraneliftType)>,
}

impl VariableBuilder {
    pub(crate) fn new() -> Self {
        Self {
            index: 0,
            variables: HashMap::new(),
        }
    }

    pub(crate) fn create_var(&mut self, builder: &mut FunctionBuilder, value: Value, ty: (crate::compiler::cranelift::types::CraneliftType, ir::Type), name: String) -> Variable {
        let variable = Variable::new(self.index);

        let _ = builder.try_declare_var(variable, ty.1);
        builder.def_var(variable, value);

        self.variables.insert(name, (self.index, variable, ty.0));

        self.index += 1;

        variable
    }

    fn set_var(&mut self, builder: &mut FunctionBuilder, name: &String, value: Value) {
        let variable = self.variables.get(name).unwrap();

        builder.def_var(variable.1, value)
    }

    pub(crate) fn get_var(&self, builder: &mut FunctionBuilder, name: &String) -> Option<(Value, crate::compiler::cranelift::types::CraneliftType)> {
        let variable = self.variables.get(name)?;

        Some((builder.use_var(variable.1), variable.2.clone()))
    }
}