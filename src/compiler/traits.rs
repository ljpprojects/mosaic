use std::any::Any;
use std::collections::{BTreeSet, HashMap, HashSet};
use crate::compiler::cranelift::module::CraneliftModule;
use crate::parser::{ParseType, TypeBound};
use cranelift_codegen::isa::OwnedTargetIsa;
use std::fmt::Display;
use std::path::PathBuf;
use std::rc::Rc;
use downcast_rs::{impl_downcast, Downcast, DowncastSync};
use crate::compiler::cranelift::CraneliftGenerator;
use crate::compiler::cranelift::meta::FunctionMeta;
use crate::compiler::cranelift::types::CraneliftType;
use crate::errors::CompilationError;

pub trait CompilationType: Display + Any + Downcast {
    fn is_numeric(&self) -> bool;
    fn is_pointer(&self) -> bool;
    fn is_c_abi(&self) -> bool;
    fn is_signed(&self) -> bool;

    fn nullable(&self) -> bool;
    fn mutable(&self) -> bool;

    fn into_c_abi(self) -> CraneliftType;

    fn to_unsigned(&self) -> Option<CraneliftType>;

    fn size_bytes(&self, isa: &OwnedTargetIsa) -> u8;
    fn size_bits(&self, isa: &OwnedTargetIsa) -> u8;

    fn inner(&self) -> Option<CraneliftType>;

    fn pseudo(&self) -> Option<CraneliftType>;

    fn cmp_eq(&self, other: &CraneliftType) -> bool;
    fn matches_bound(&self, bound: TypeBound, generator: &CraneliftGenerator, allowed_tgs: &HashMap<String, Option<TypeBound>>) -> Result<bool, Box<[CompilationError]>>;
    fn iterable(&self) -> bool;
}

impl_downcast!(CompilationType);

pub trait TypeGenerator: Downcast {
    fn merge(&mut self, other: &dyn TypeGenerator);
    fn register_type(&mut self, name: &String, ty: CraneliftType);

    fn get_type(&self, name: &String) -> CraneliftType;
    fn compile_type_no_tgs(&self, ty: &ParseType, isa: &OwnedTargetIsa) -> CraneliftType;

    fn compile_type(&self, ty: &ParseType, isa: &OwnedTargetIsa, tgs: &HashMap<String, Option<TypeBound>>) -> CraneliftType;

    fn types(&self) -> &HashMap<String, CraneliftType>;
}

impl_downcast!(TypeGenerator);

pub trait CompilationModule {
    fn lookup_func(&self, name: &String) -> Option<&FunctionMeta>;
    fn lookup_func_variants(&self, name: &String) -> Option<Vec<(CraneliftType, Vec<CraneliftType>)>>;

    fn assoc_obj(&self) -> Option<PathBuf>;
    fn name(&self) -> String;
    fn prev_includes(&self) -> &BTreeSet<CraneliftModule>;
    fn mosaic_file(&self) -> PathBuf;
    fn functions(&self) -> HashMap<String, FunctionMeta>;
    fn function_variants(&self) -> HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>>;
    fn tg(&self) -> Box<&dyn TypeGenerator>;
    fn out_file(&self) -> PathBuf;
}
