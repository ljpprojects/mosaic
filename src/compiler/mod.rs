use std::collections::HashMap;
use std::error::Error;
use std::fmt::Display;
use std::path::PathBuf;
use std::str::FromStr;
use ::qbe::Function;
use crate::cli::Flag;
use crate::parser::{AstNode, TypeBound};
use crate::utils::UseSparingly;

pub mod qbe;

pub trait ValueType<'a>: ToString + PartialEq + Clone + Display + FromStr {
    type Gen: Generator<'a>;
    
    fn size(&self) -> u64;
    fn matches_bound(&self, bound: TypeBound, generator: &'a mut Self::Gen, allowed_tgs: &HashMap<String, Option<TypeBound>>) -> Result<bool, impl GenerationError>;
    fn from_iter<I: Iterator<Item=char>>(iter: &mut I) -> Result<Self, impl GenerationError>;
}

pub trait Value<'a>: Clone + PartialEq {
    type ValType: ValueType<'a>;
    
    fn get_type(&self) -> Self::ValType;
    fn set_type(&mut self, ty: Self::ValType) -> UseSparingly<()>;
    
    fn byte(b: i8) -> Self;
    fn short(b: i16) -> Self;
    fn word(b: i32) -> Self;
    fn long(b: i64) -> Self;

    fn float(b: f32) -> Self;
    fn double(b: f64) -> Self;
}

pub trait GenerationError: Error + Clone + Display {}

pub trait GeneratedModule: Clone + PartialEq + ToString {
    fn name(&self) -> String;
    fn version(&self) -> Option<String>;
    fn author(&self) -> Option<String>;
    fn repo(&self) -> Option<String>;
    fn flags(&self) -> Vec<Flag>;
    
    fn entry_file(&self) -> PathBuf;
    fn assoc_obj_file(&self) -> Option<PathBuf>;
    
    fn out_obj_path(&self) -> PathBuf;
    fn out_ir_path(&self) -> PathBuf;
    
    fn get_ir_repr(&self) -> String {
        self.to_string()
    }
}

pub trait Generator<'a> {
    fn generate(&'a mut self) -> Result<impl GeneratedModule, impl GenerationError>;
    fn generate_expr(&'a mut self, expr: AstNode, func: &mut Function<'a>) -> Result<impl Value, impl GenerationError>; 
    fn types(&self) -> HashMap<String, impl ValueType<'a>>;
}

pub trait Mangle: Clone {
    fn mangle(&self) -> String;
    fn from_mangled(mangled: String) -> Option<Self>;
}

pub trait Linker: Clone + PartialEq {
    fn modules(&self) -> Vec<impl GeneratedModule>;
    fn add_module(&mut self, module: impl GeneratedModule);
    fn link(&self) -> Result<(), Box<dyn Error>>;
}

impl<'a, VT: ValueType<'a>> Mangle for (String, VT, Vec<VT>) {
    fn mangle(&self) -> String {
        format!("{R}_{A}_{N}", R = self.1, A = self.2.iter().map(|vt| vt.to_string()).collect::<Vec<String>>().join("_"), N = self.0)
    }

    fn from_mangled(mangled: String) -> Option<Self> {
        let mut iter = mangled.chars();

        let ret_type = VT::from_iter(&mut iter).ok()?;
        let mut arg_types: Vec<VT> = vec![];

        iter.next()?;

        loop {
            let Ok(ty) = VT::from_iter(&mut iter) else {
                break
            };

            arg_types.push(ty);
        }

        let name = iter.collect::<String>();

        Some((name, ret_type, arg_types))
    }
}