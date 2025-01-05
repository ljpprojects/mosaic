use crate::compiler::cranelift::types::TypeGenerator;
use crate::compiler::cranelift::FunctionMeta;
use cranelift_object::ObjectProduct;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::path::PathBuf;

pub struct CraneliftModule {
    pub product: ObjectProduct,
    pub assoc_obj: Option<PathBuf>,
    pub name: String,
    pub prev_includes: HashSet<(PathBuf, Option<PathBuf>)>,
    pub mosaic_file: PathBuf,
    pub functions: HashMap<String, Vec<FunctionMeta>>,
    pub tg: TypeGenerator,
    pub out_file: PathBuf,
}

impl Debug for CraneliftModule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "MODULE {}", self.name)?;
        writeln!(f, "\tASSOC_OBJ: {:?}", self.assoc_obj)?;
        writeln!(f, "\tMOSAIC_FILE: {:?}", self.mosaic_file)?;
        writeln!(f, "\tOUT_FILE: {:?}", self.out_file)?;
        writeln!(f, "\tPREV_INCLUDES: {:?}", self.prev_includes)?;
        writeln!(f, "\tFUNCTIONS: {:?}", self.functions)
    }
}

impl CraneliftModule {
    pub fn lookup_func(&self, name: &String) -> Option<&Vec<FunctionMeta>> {
        self.functions.get(name)
    }
}
