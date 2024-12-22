use std::collections::HashMap;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir;
use cranelift_codegen::ir::{Type, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use crate::compiler::cranelift::types::CraneliftType;

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

    pub fn declare_var(&mut self, builder: &mut FunctionBuilder, ty: (CraneliftType, Type), name: String) -> Variable {
        let variable = Variable::new(self.index);

        builder.declare_var(variable, ty.1);

        self.variables.insert(name, (self.index, variable, ty.0));

        self.index += 1;

        variable
    }

    pub fn create_var(&mut self, builder: &mut FunctionBuilder, value: Value, ty: (CraneliftType, ir::Type), name: String) -> Variable {
        let variable = Variable::new(self.index);
        
        builder.declare_var(variable, ty.1);
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