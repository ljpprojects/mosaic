#![feature(ptr_as_ref_unchecked)]
#![feature(arbitrary_self_types)]
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

extern crate core;
extern crate test;

use std::str::FromStr;
use cranelift_codegen::isa;
use cranelift_codegen::isa::IsaBuilder;
use crate::compiler::cranelift::linker::Linker;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use cranelift_native;
use target_lexicon::Triple;

pub mod cli;
pub mod compiler;
pub mod errors;
pub mod file;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;

const F_NAME: &str = "/Users/geez/RustroverProjects/mosaic/examples/hello.msc";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let reader = CharReader::new(File::new(F_NAME.to_string()).unwrap());
    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    let cg = CraneliftGenerator::new(parser, isa::lookup(Triple::from_str("aarch64-linux-gnu").unwrap())?);

    match cg.compile(true, None) {
        Ok(gen) => Linker::link(gen),
        Err(errors) => {
            for err in errors {
                eprintln!("{err}")
            }
        }
    }

    Ok(())
}
