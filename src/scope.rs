use std::collections::HashMap;

use crate::runtime::values::RuntimeValue;
use crate::runtime::types::Type;
use crate::utils::{Indirection, MutRc};

pub struct Scope<'a> {
    parent: Option<MutRc<Scope<'a>>>,
    variables: HashMap<String, (RuntimeValue<'a>, Type<'a>)>
}

impl<'a> Scope<'a> {
    pub fn new(parent: Option<MutRc<Scope<'a>>>) -> Scope<'a> {
        Scope { parent, variables: HashMap::new() }
    }
    
    pub fn set_var(&mut self, name: &str, value: RuntimeValue<'a>, var_type: Type<'a>) {
        self.variables.insert(String::from(name), (value, var_type));
    }

    pub fn get_var(&self, name: &str) -> Option<&(RuntimeValue, Type)> {
        match self.variables.get(name) {
            Some(v) => Some(v),
            None => {
                if let Some(ref parent) = self.parent {
                    parent.get_var(name)
                } else {
                    None
                }
            }
        }
    }

    pub fn get_var_mut(&mut self, name: &str) -> Option<MutRc<(RuntimeValue<'a>, Type<'a>)>> {
        match self.variables.get_mut(name) {
            Some(v) => Some(MutRc::new(v.clone())),
            None => {
                if let Some(ref mut parent) = self.parent {
                    parent.get_var_mut(name)
                } else {
                    None
                }
            }
        }
    }

    pub fn parent(&self) -> Option<&MutRc<Scope<'a>>> {
        self.parent.as_ref()
    }
}