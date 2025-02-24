use crate::compiler::cranelift::types::{CraneliftType, CraneliftTypeGenerator};
use crate::compiler::cranelift::FunctionMeta;
use crate::compiler::traits;
use crate::compiler::traits::{CompilationModule, CompilationType};
use cranelift_object::ObjectProduct;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::path::PathBuf;
use std::rc::Rc;

pub struct CraneliftModule {
    pub product: ObjectProduct,
    pub assoc_obj: Option<PathBuf>,
    pub name: String,
    pub prev_includes: HashSet<(PathBuf, Option<PathBuf>)>,
    pub mosaic_file: PathBuf,
    pub functions: HashMap<String, FunctionMeta>,
    pub function_variants: HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>>,
    pub tg: CraneliftTypeGenerator,
    pub out_file: PathBuf,
}

impl CompilationModule for CraneliftModule {
    fn lookup_func(&self, name: &String) -> Option<&FunctionMeta> {
        self.functions.get(name)
    }
    
    fn lookup_func_variants(&self, name: &String) -> Option<Vec<(Box<dyn CompilationType>, Vec<Box<dyn CompilationType>>)>> {
        Some(self.function_variants.get(name)?.iter().map(|(a, b)| (Box::new(a.clone()) as Box<dyn CompilationType>, b.iter().map(|b| Box::new(b.clone()) as Box<dyn CompilationType>).collect::<Vec<_>>())).collect())
    }

    fn assoc_obj(&self) -> Option<PathBuf> {
        self.assoc_obj.clone()
    }

    fn name(&self) -> String {
        self.name.clone()
    }

    fn prev_includes(&self) -> HashSet<(PathBuf, Option<PathBuf>)> {
        self.prev_includes.clone()
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
        Box::new(&self.tg as &dyn traits::TypeGenerator)
    }

    fn out_file(&self) -> PathBuf {
        todo!()
    }
}
