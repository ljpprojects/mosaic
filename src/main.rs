use std::alloc::alloc;
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
use std::ptr::null;
use std::str::FromStr;
use std::thread;
use cranelift_codegen::gimli;
use cranelift_codegen::isa::lookup;
use target_lexicon::{Architecture, Triple};

pub mod cli;
pub mod compiler;
pub mod file;
pub mod frontend;
pub mod reader;
pub mod states;
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
                None,
                None
            );

            match cg.compile(true, None) {
                Ok(gen) => match Linker::link(gen, args.command, triple) {
                    Ok(_) => Ok::<(), Box<dyn std::error::Error>>(()),
                    Err(e) => {
                        panic!("{e}")
                    },
                },
                Err(errors) => {
                    for err in errors {
                        eprintln!("{err}")
                    }

                    exit(1)
                }
            }
        }?
    }

    // thread::spawn(|| null());

    Ok(())
}
