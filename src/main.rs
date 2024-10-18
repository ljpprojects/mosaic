#![feature(ptr_as_ref_unchecked)]
#![feature(test)]

#[allow(invalid_reference_casting)]
extern crate test;

use crate::lexer::StreamedLexer;
use crate::reader::CharReader;
use std::cell::Cell;
use std::fs::File;
use std::io::Read;
use crate::parser::StreamedParser;

mod lexer;
mod reader;
pub mod tokens;
mod macros;
mod parser;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut reader = Cell::new(CharReader::new(File::open("/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic").unwrap()));

    let mut lexer = StreamedLexer::new(reader.as_ptr());
    let mut parser = StreamedParser::new(&mut lexer);

    for node in parser {
        println!("{:?}", node)
    }

    Ok(())
}

mod tests {
    use std::cell::Cell;
    use std::fs::File;
    use crate::lexer::StreamedLexer;
    use crate::parser::StreamedParser;
    use crate::reader::CharReader;

    #[test]
    fn peek_token() -> () {
        let mut reader = Cell::new(CharReader::new(File::open("examples/bench.mosaic").unwrap()));

        let mut lexer = StreamedLexer::new(reader.as_ptr());
        let mut parser = StreamedParser::new(&mut lexer);

        let node = parser.next_ast_node().unwrap().unwrap();
    }
}