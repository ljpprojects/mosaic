use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;
use qbe::{DataDef, Function, Module, TypeDef};
use crate::cli::Flag;
use crate::compiler::GeneratedModule;
use crate::compiler::qbe::FunctionMeta;
use crate::compiler::qbe::types::QbeType;

#[derive(Debug, Clone, PartialEq)]
pub struct QbeModule<'a> {
    module: Module<'a>,
    pub typedefs: Vec<TypeDef<'a>>,
    pub functions: HashMap<String, FunctionMeta<'a>>,
    pub datadefs: Vec<DataDef<'a>>,
    
    name: String,
    
    // a path to the Mosaic entry point of this module
    entry_point: PathBuf,
    
    // a path to an associated object file (for FFI)
    assoc_obj_file: Option<PathBuf>,
    
    pub included_modules: Vec<QbeModule<'a>>,
    
    /******** Scraped from module.toml (if it exists) ********/
    /********   For now these are always None/empty   ********/
    
    version: Option<String>,
    repo: Option<String>,
    author: Option<String>,
    flags: Vec<Flag>
}

impl Display for QbeModule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module)
    }
}

impl<'a> QbeModule<'a> {
    pub fn new(
        name: String,
        module: Module<'a>,
        entry_point: PathBuf,
        flags: Vec<Flag>,
        included_modules: Vec<QbeModule<'a>>,
        typedefs: Vec<TypeDef<'a>>,
        functions: HashMap<String, FunctionMeta<'a>>,
        datadefs: Vec<DataDef<'a>>
    ) -> Self {
        Self {
            included_modules,
            module,
            name,
            entry_point,
            assoc_obj_file: None,
            version: None,
            repo: None,
            author: None,
            flags,
            functions,
            typedefs,
            datadefs,
        }
    }
}

impl<'a> GeneratedModule for QbeModule<'a> {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn version(&self) -> Option<String> {
        self.version.clone()
    }

    fn author(&self) -> Option<String> {
        self.author.clone()
    }

    fn repo(&self) -> Option<String> {
        self.repo.clone()
    }
    
    fn flags(&self) -> Vec<Flag> {
        self.flags.clone()
    }

    fn entry_file(&self) -> PathBuf {
        self.entry_point.clone()
    }
    
    fn assoc_obj_file(&self) -> Option<PathBuf> {
        self.assoc_obj_file.clone()
    }

    fn out_obj_path(&self) -> PathBuf {
        let mut tmp = self.entry_file().clone();
        
        tmp.set_extension("msc.o");
        
        tmp
    }

    fn out_ir_path(&self) -> PathBuf {
        let mut tmp = self.entry_file().clone();

        tmp.set_extension("msc.ssa");

        tmp
    }
}