#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]

extern crate core;

use crate::cli::{Args, Command};
use crate::compiler::cranelift::linker::Linker;
use crate::compiler::cranelift::trace::Trace;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::errors::CompilationError;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use clap::Parser;
use std::path::PathBuf;
use std::process::exit;
use std::str::FromStr;
use cranelift_codegen::isa::lookup;
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

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match args.command.clone() {
        Command::Finish => todo!("Implement 'finish' command, for now, clone the mosaic-std and mosaic-core modules into the appropriate directory as std and core."),

        Command::Build { file, target, .. } => {
            let triple = Triple::from_str(&target.unwrap_or("_".into())).unwrap_or(Triple::host());

            if !PathBuf::from(file.clone()).exists() {
                return Err(CompilationError::UnknownModule(
                    PathBuf::from(file.clone()),
                    Trace::new_root("GLOBAL".into()),
                    vec![file].into(),
                )
                    .into());
            }

            let reader = CharReader::new(File::new(file)?);
            let lexer = StreamedLexer::new(reader);
            let parser = StreamedParser::new(lexer);

            let cg = CraneliftGenerator::new(
                parser,
                lookup(triple.clone())?,
                Some(args.command.clone()),
            );

            match cg.compile(true, None) {
                Ok(gen) => Linker::link(gen, args.command, triple),
                Err(errors) => {
                    for err in errors {
                        eprintln!("{err}")
                    }

                    exit(1)
                }
            }
        }?
    }

    Ok(())
}
