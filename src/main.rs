#![feature(let_chains)]
#![feature(exitcode_exit_method)]
#![feature(slice_pattern)]

extern crate core;

use crate::cli::{Args, Command};
use crate::compiler::cranelift::linker::Linker;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use clap::Parser;
use cranelift_native;
use std::process::ExitCode;
use std::str::FromStr;

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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    
    let Command::Build { file, .. } = args.command.clone();

    let reader = CharReader::new(File::new(file).unwrap());
    let lexer = StreamedLexer::new(reader);
    let parser = StreamedParser::new(lexer);

    let cg = CraneliftGenerator::new(
        parser,
        cranelift_native::builder()?,
        Some(args.command.clone()),
    );

    match cg.compile(true, None) {
        Ok(gen) => Linker::link(gen, args.command),
        Err(errors) => {
            for err in errors {
                eprintln!("{err}")
            }

            ExitCode::FAILURE.exit_process()
        }
    }

    ExitCode::SUCCESS.exit_process()
}
