#![feature(let_chains)]
extern crate core;

use crate::compiler::cranelift::linker::Linker;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use cranelift_codegen::isa;
use cranelift_native;
use std::str::FromStr;
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

    let cg = CraneliftGenerator::new(parser, cranelift_native::builder()?);

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
