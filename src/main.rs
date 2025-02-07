#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]

extern crate core;

use http_body_util::BodyExt;
use std::fs;
use std::io::Write;
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
use cranelift_native;
use std::path::PathBuf;
use std::process::{exit, ExitCode, Termination};
use flate2::read::GzDecoder;
use octocrab::Octocrab;
use octocrab::params::repos::Reference;
use tar::Archive;

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
mod schema_capnp;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match args.command.clone() {
        Command::Finish => {
            let core_path = PathBuf::from(format!("{}/.msc/mods/core", env!("HOME")));
            let std_path = PathBuf::from(format!("{}/.msc/mods/std", env!("HOME")));

            let octocrab = Octocrab::builder().build()?;

            let _ = fs::create_dir(format!("{}/.msc/tmp", env!("HOME")));

            let mut resp = octocrab
                .repos("ljp-projects", "mosaic-core")
                .download_tarball(Reference::Branch("main".to_owned()))
                .await?;

            let body = resp.body_mut();

            let mut file = fs::File::create(format!("{}/.msc/tmp/core.tar.gz", env!("HOME")))?;

            while let Some(next) = body.frame().await {
                let frame = next?;
                if let Some(chunk) = frame.data_ref() {
                    file.write_all(chunk)?;
                }
            }

            let tar = GzDecoder::new(file);
            let mut archive = Archive::new(tar);

            archive.unpack(core_path)?;

            let mut resp = octocrab
                    .repos("ljp-projects", "mosaic-std")
                    .download_tarball(Reference::Branch("main".to_owned()))
                    .await?;

            let body = resp.body_mut();

            let mut file = fs::File::create(format!("{}/.msc/tmp/std.tar.gz", env!("HOME")))?;

            while let Some(next) = body.frame().await {
                let frame = next?;
                if let Some(chunk) = frame.data_ref() {
                    file.write_all(chunk)?;
                }
            }

            let tar = GzDecoder::new(file);
            let mut archive = Archive::new(tar);

            archive.unpack(std_path)?;
        }

        Command::Build { file, .. } => {
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
                cranelift_native::builder()?,
                Some(args.command.clone()),
            );

            match cg.compile(true, None) {
                Ok(gen) => Linker::link(gen, args.command),
                Err(errors) => {
                    for err in errors {
                        eprintln!("{err}")
                    }

                    exit(1)
                }
            }
        }
    }

    Ok(())
}
