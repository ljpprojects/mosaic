use crate::compiler::cranelift::types::{CraneliftType, CraneliftTypeGenerator};
use crate::compiler::cranelift::FunctionMeta;
use crate::compiler::traits;
use crate::compiler::traits::{CompilationModule, CompilationType};
use cranelift_object::ObjectProduct;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::path::PathBuf;
use std::rc::Rc;
use crate::compiler::cranelift::meta::DataDeclMeta;

#[derive(Clone)]
pub struct CraneliftModule {
    pub product: Rc<ObjectProduct>,
    pub assoc_obj: Option<PathBuf>,
    pub name: String,
    pub prev_includes: BTreeSet<CraneliftModule>,
    pub mosaic_file: PathBuf,
    pub functions: HashMap<String, FunctionMeta>,
    pub data_declarations: HashMap<String, DataDeclMeta>,
    pub function_variants: HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>>,
    pub tg: Rc<CraneliftTypeGenerator>,
    pub out_file: PathBuf,
}

impl PartialEq for CraneliftModule {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
        && self.assoc_obj == other.assoc_obj
        && self.prev_includes == other.prev_includes
        && self.mosaic_file == other.mosaic_file
        && self.out_file == other.out_file
        && self.functions == other.functions
        && self.tg.as_ref() == other.tg.as_ref()
        && self.function_variants == other.function_variants
        && self.product.data_objects == other.product.data_objects
        && self.product.functions == other.product.functions
        && self.product.object.write().is_ok_and(|a| other.product.object.write().is_ok_and(|b| a == b))
        && self.data_declarations == other.data_declarations
    }
}

impl Eq for CraneliftModule {}

impl PartialOrd for CraneliftModule {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl Ord for CraneliftModule {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl CompilationModule for CraneliftModule {
    fn lookup_func(&self, name: &String) -> Option<&FunctionMeta> {
        self.functions.get(name)
    }

    fn lookup_func_variants(&self, name: &String) -> Option<Vec<(CraneliftType, Vec<CraneliftType>)>> {
        Some(self.function_variants.get(name)?.iter().map(|(a, b)| (a.clone(), b.iter().cloned().collect::<Vec<_>>())).collect())
    }

    fn assoc_obj(&self) -> Option<PathBuf> {
        self.assoc_obj.clone()
    }

    fn name(&self) -> String {
        self.name.clone()
    }

    fn prev_includes(&self) -> &BTreeSet<CraneliftModule> {
        &self.prev_includes
    }

    fn mosaic_file(&self) -> PathBuf {
        self.mosaic_file.clone()
    }

    fn functions(&self) -> HashMap<String, FunctionMeta> {
        self.functions.clone()
    }

    fn function_variants(&self) -> HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>> {
        self.function_variants.clone()
    }

    fn tg(&self) -> Box<&dyn traits::TypeGenerator> {
        Box::new(&*self.tg as &dyn traits::TypeGenerator)
    }

    fn out_file(&self) -> PathBuf {
        self.out_file.clone()
    }
}
