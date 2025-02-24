use clap::{Parser, Subcommand, ValueEnum};

#[derive(Clone, Debug, Copy, PartialEq, Eq, ValueEnum)]
pub enum EmitKind {
    #[value(name = "bin")]
    Binary,
    
    #[value(name = "sbin")]
    StaticBinary,

    #[value(name = "slib")]
    StaticLib,

    #[value(name = "dylib")]
    DynamicLib,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, ValueEnum)]
pub enum Backend {
    #[value(name = "cranelift")]
    Cranelift,

    #[value(name = "javascript")]
    JavaScript,
}

#[derive(Subcommand, Debug, Clone, PartialEq, Eq)]
pub enum Command {
    Build {
        file: String,

        #[arg(short = 'o', long = "out-file")]
        out_file: Option<String>,

        #[arg(short = 'l')]
        libraries: Vec<String>,

        #[arg(long = "ld-args")]
        link_flags: Option<String>,

        #[arg(long = "shell-path", default_value = "/bin/sh")]
        shell_path: String,

        #[arg(long = "shell-eval-flag", default_value = "-c")]
        shell_eval_flag: String,
        
        #[arg(long = "no-implicit-functions")]
        no_implicit_functions: bool,

        #[arg(short = 'q', long = "quiet")]
        quiet: bool,
        
        #[arg(long = "emit", default_value = "bin")]
        emit: EmitKind,
        
        #[arg(long = "target")]
        target: Option<String>,
        
        #[arg(long = "linker", default_value = "ld")]
        linker: String,
    },

    Finish,
}

#[derive(Parser, Debug, Clone, PartialEq, Eq)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[command(subcommand)]
    pub command: Command,
}
