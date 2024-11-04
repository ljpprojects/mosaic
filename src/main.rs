#![forbid(unsafe_code)]
#![feature(ptr_as_ref_unchecked)]
#![feature(test)]

#[allow(invalid_reference_casting)]
extern crate test;

use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;

mod file;
mod lexer;
mod macros;
mod parser;
mod reader;
mod states;
pub mod tokens;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let reader = CharReader::new(
        File::new("/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic".to_string())
            .unwrap(),
    );

    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    for node in parser {
        println!("[NODE] {:#?}", node?)
    }

    Ok(())
}
