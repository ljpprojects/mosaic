use std::collections::HashMap;
use crate::parser::{ParseType, TypeBound};
use cranelift_codegen::isa::OwnedTargetIsa;
use std::fmt::Display;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::errors::CompilationError;

pub trait CompilationType: ToString + Display + Sized + Clone + PartialEq {
    fn is_numeric(&self) -> bool;
    fn is_pointer(&self) -> bool;
    fn is_c_abi(&self) -> bool;
    fn is_signed(&self) -> bool;
    
    fn into_c_abi(self) -> Self;
    
    fn to_unsigned(&self) -> Option<Self>;

    fn size_bytes(&self, isa: &OwnedTargetIsa) -> u8;
    fn size_bits(&self, isa: &OwnedTargetIsa) -> u8;

    fn inner(&self) -> Option<Self>;

    fn pseudo(&self) -> Option<Self>;

    fn cmp_eq(&self, other: &Self) -> bool;
    fn matches_bound(&self, bound: TypeBound, generator: &CraneliftGenerator, allowed_tgs: &HashMap<String, Option<TypeBound>>) -> Result<bool, Box<[CompilationError]>>;
    fn iterable(&self) -> bool;
}

pub trait TypeGenerator<T: CompilationType> {
    fn merge(&mut self, other: &Self);
    fn register_type(&mut self, name: String, ty: T);
    fn compile_type(&self, ty: &ParseType, isa: &OwnedTargetIsa);
}
