#![feature(ptr_as_ref_unchecked)]
#![feature(test)]
#![feature(f128)]
#![feature(let_chains)]
#![feature(unsized_locals)]
#![feature(associated_type_defaults)]
#![feature(sized_type_properties)]
#![allow(invalid_reference_casting)]
#![allow(incomplete_features)]
#![allow(refining_impl_trait)]

extern crate test;
extern crate core;

use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::rc::Rc;
use colored::Colorize;
use cranelift_native;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::compiler::cranelift::linker::Linker;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use crate::tokens::LineInfo;

pub mod compiler;
pub mod file;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;
pub mod cli;
pub mod errors;

const F_NAME: &str = "/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let reader = CharReader::new(File::new("./examples/hello.msc".to_string()).unwrap());
    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    let mut cg = CraneliftGenerator::new(parser, cranelift_native::builder()?, "bench".into());

    let gen = cg.compile(true, None)?;
    
    Linker::link(gen);

    /*let reader = CharReader::new(File::new(PathBuf::from("examples/hello.msc").to_string_lossy().to_string()).unwrap());

    print!("{}", reader.get_snippet(&LineInfo::new(
        Rc::new(NonZeroUsize::new(1).unwrap()),
        Rc::new(NonZeroUsize::new(19).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
    )).unwrap());

    print!("{}", reader.get_snippet(&LineInfo::new(
        Rc::new(NonZeroUsize::new(19).unwrap()),
        Rc::new(NonZeroUsize::new(22).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
    )).unwrap().red().bold());

    println!("{}", reader.get_snippet(&LineInfo::new(
        Rc::new(NonZeroUsize::new(22).unwrap()),
        Rc::new(NonZeroUsize::new(33).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
        Rc::new(NonZeroUsize::new(1).unwrap()),
    )).unwrap());*/
    
    Ok(())
}
