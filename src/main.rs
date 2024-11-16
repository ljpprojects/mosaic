
#![feature(ptr_as_ref_unchecked)]
#![feature(test)]
#![allow(invalid_reference_casting)]

extern crate test;

use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;

pub mod file;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let reader = CharReader::new(
        File::new("/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic".to_string())
            .unwrap(),
    );

    let lexer = StreamedLexer::new(reader);
    let mut parser = StreamedParser::new(lexer);

    while let Some(Ok(node)) = parser.next_ast_node() {
        println!("{}", &node);
    }

    Ok(())
}
