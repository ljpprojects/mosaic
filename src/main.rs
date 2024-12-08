#![feature(ptr_as_ref_unchecked)]
#![feature(test)]
#![feature(f128)]
#![feature(let_chains)]
#![feature(unsized_locals)]
#![allow(invalid_reference_casting)]
#![allow(incomplete_features)]

extern crate test;

use crate::compiler::linker::Linker;

pub mod compiler;
pub mod file;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let f_name = "/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic".to_string();
    let linker = Linker::new(f_name.parse().unwrap(), "bench");

    linker.link().unwrap();

    Ok(())
}
