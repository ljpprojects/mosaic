use crate::parser::AstNode;
use std::collections::HashMap;

/// Stores data about the indexed module.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IndexTable {
    /// The version of the index table.
    version: u16,

    /// The name of the indexed module.
    module_name: String,

    /// Any submodules, e.g. foo::bar is a submodule of foo.
    submodules: Vec<IndexTable>,

    /// The mangled names of functions in this module.
    functions: Vec<String>,

    /// Any modules included in the file
    includes: Vec<String>,

    /// The mangled versions of types declared in the module
    types: HashMap<String, String>,
}