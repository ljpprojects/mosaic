use clap::{Parser, Subcommand, ValueEnum};

#[derive(Clone, Debug, Copy, PartialEq, Eq, ValueEnum)]
pub enum EmitKind {
    #[value(name = "bin")]
    Binary,

    #[value(name = "static")]
    StaticLib,

    #[value(name = "dynamic")]
    DynamicLib,
}

#[derive(Subcommand, Debug, Clone, PartialEq, Eq)]
pub enum Command {
    Build {
        file: String,

        #[arg(short = 'o', long = "out-file")]
        out_file: Option<String>,

        #[arg(short = 'l')]
        libraries: Vec<String>,

        /// {INP} = input files
        /// {DST} = output file
        /// {LIB} = library files (included & -l)
        #[arg(
            long = "link-with",
            default_value = "gcc -Wl,-O3,-pie -o {DST} {INP} {LIB}"
        )]
        link_command: String,

        #[arg(long = "shell-path", default_value = "/bin/sh")]
        shell_path: String,

        #[arg(long = "shell-eval-flag", default_value = "-c")]
        shell_eval_flag: String,
        
        #[arg(long = "no-implicit-functions")]
        no_implicit_functions: bool,

        #[arg(short = 'q', long = "quiet")]
        quiet: bool,
        
        #[arg(long = "emit")]
        emit: EmitKind,
    },

    Finish,
}

#[derive(Parser, Debug, Clone, PartialEq, Eq)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[command(subcommand)]
    pub command: Command,
}
