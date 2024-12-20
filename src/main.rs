#![feature(ptr_as_ref_unchecked)]
#![feature(test)]
#![feature(f128)]
#![feature(let_chains)]
#![feature(unsized_locals)]
#![feature(associated_type_defaults)]
#![feature(sized_type_properties)]
#![feature(strict_provenance)]
#![allow(invalid_reference_casting)]
#![allow(incomplete_features)]
#![allow(refining_impl_trait)]

extern crate test;
extern crate core;

use std::path::PathBuf;
use cranelift_native;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::compiler::cranelift::errors::CraneliftError;
use crate::compiler::cranelift::linker::Linker;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;

pub mod compiler;
pub mod file;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;
pub mod cli;

const F_NAME: &str = "/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    /*
    let reader = CharReader::new(File::new("./examples/hello.msc".to_string()).unwrap());
    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    let mut cg = CraneliftGenerator::new(parser, cranelift_native::builder()?, "bench".into());

    cg.compile(true, None);
    */
    
    let file = PathBuf::from("test.msc");
    
    println!("{}", CraneliftError::UnknownModule(file.clone(), vec!["test".to_string()].into_boxed_slice()));

    println!();
    println!("{}", CraneliftError::UndefinedVariable(file.clone(), "foo".into()));

    println!();
    println!("{}", CraneliftError::DualDefinition(file.clone(), "bar".into()));
    
    Ok(())
}
