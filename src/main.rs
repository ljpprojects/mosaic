
#![feature(ptr_as_ref_unchecked)]
#![feature(test)]

#[allow(invalid_reference_casting)]
extern crate test;

use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use crate::runtime::eval::eval;
use crate::scope::Scope;

pub mod file;
pub mod lexer;
pub mod macros;
pub mod parser;
pub mod reader;
pub mod states;
pub mod tokens;
pub mod utils;
pub mod scope;
pub mod runtime;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let reader = CharReader::new(
        File::new("/Users/geez/RustroverProjects/mosaic/examples/bench.mosaic".to_string())
            .unwrap(),
    );

    let lexer = StreamedLexer::new(reader);
    let mut parser = StreamedParser::new(lexer);
    let scope = &mut Scope::new(None);

    while let Some(Ok(node)) = parser.next_ast_node() {
        eval(scope, &node);
    }
    
    println!("{:?}", scope.get_var("foo"));
    println!("{:?}", scope.get_var("bar"));

    Ok(())
}
