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

use std::fmt::Debug;
use std::io;
use std::ptr::addr_of;
use std::sync::LazyLock;
use compiler::qbe::linker::QbeLinker;
use crate::compiler::qbe::QbeGenerator;
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
mod cli;

const F_NAME: &str = "/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic";

static mut GENERATOR: LazyLock<QbeGenerator<'static>, fn() -> QbeGenerator<'static>> = LazyLock::new(|| {
    let reader = CharReader::new(File::new(F_NAME.to_string()).unwrap());
    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    QbeGenerator::new(parser, None)
});

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let linker = QbeLinker::new(F_NAME.parse().unwrap(), "bench");
    
    unsafe { linker.link((addr_of!(GENERATOR) as *const QbeGenerator<'static> as *mut QbeGenerator<'static>).as_mut().unwrap()).unwrap(); }

    Ok(())
}
