use crate::compiler::cranelift::types::CraneliftType;
use crate::parser::AstNode;
use crate::tokens::{LineInfo, Token};
use colored::Colorize;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;

#[derive(Clone)]
pub enum CompilationError {
    /**** Lex errors ****/
    InvalidChar(PathBuf, char, LineInfo),
    UnfinishedString(PathBuf, LineInfo),
    TooManyLines(PathBuf),

    /**** Parse errors ****/
    ExpectedToken(PathBuf, Token, Token),
    UnexpectedEOF(PathBuf, Token),
    InvalidNode(PathBuf, AstNode),
    InvalidToken(PathBuf, Token),
    Forbidden(PathBuf, String),

    /**** Compilation errors ****/
    UnknownModule(PathBuf, Box<[String]>),
    UndefinedVariable(PathBuf, String),
    DualDefinition(PathBuf, String),
    UndefinedOperator(PathBuf, String),
    MismatchedTypeInDef(PathBuf, String, CraneliftType, CraneliftType),
    CannotMutate(PathBuf, String),
    UndefinedFunction(PathBuf, String),
}

impl Error for CompilationError {}

impl Debug for CompilationError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for CompilationError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            CompilationError::InvalidChar(file, char, line_info) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Lexing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}{}{}",
                    "Inavalid character '".bold(),
                    char.to_string().italic().bold(),
                    "' at ".bold(),
                    line_info.to_string().bold().italic(),
                    ".".bold()
                )
            }

            CompilationError::UnfinishedString(file, line_info) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Lexing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Unfinished string beginning at".bold(),
                    line_info.to_string().bold().italic(),
                    ".".bold()
                )
            }

            CompilationError::TooManyLines(file) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Skill issue in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}",
                    "Bro there are too many lines in your file 💀".bold(),
                )?;
                writeln!(f, "    try using a  m o d u l e",)
            }

            CompilationError::ExpectedToken(file, expected, found) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}{}{}",
                    "Expected token ".bold(),
                    format!("{expected:?}").italic().bold(),
                    " but found token ".bold(),
                    format!("{found:?}").bold().italic(),
                    ".".bold()
                )
            }

            CompilationError::InvalidNode(file, node) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Invalid expression ".bold(),
                    format!("{node}").italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::InvalidToken(file, token) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Invalid token ".bold(),
                    format!("{token:?}").italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::Forbidden(file, message) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Forbidden: ".bold(),
                    format!("{message:?}").italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::UnexpectedEOF(file, expected) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Unexpected EOF; expected token ".bold(),
                    format!("{expected:?}").italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::UnknownModule(file, modules) => {
                let module = modules.join("::");

                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Module ".bold(),
                    module.italic().bold(),
                    " not found.".bold()
                )?;
                write!(
                    f,
                    "{}{}{}{}{}{}{}",
                    "    Maybe you need to install a module via ",
                    "mosaic install ".italic().yellow(),
                    modules.first().unwrap().bold().italic().yellow(),
                    " or check ",
                    modules.first().unwrap().bold(),
                    "'s documentation at ",
                    format!(
                        "https://msc.ljpprojects.org/module/{}",
                        modules.first().unwrap()
                    )
                    .bold()
                    .italic()
                    .blue()
                    .underline()
                )
            }

            CompilationError::UndefinedVariable(file, name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Variable ".bold(),
                    name.italic().bold(),
                    " is not defined.".bold()
                )?;
                write!(
                    f,
                    "{}{}{}{}",
                    "    Try adding ",
                    "def auto ".italic().yellow(),
                    name.italic().yellow(),
                    " -> VALUE".italic().yellow(),
                )
            }

            CompilationError::DualDefinition(file, name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Attempted to define variable ".bold(),
                    name.italic().bold(),
                    " multiple times.".bold()
                )?;
                write!(
                    f,
                    "    Did you mean to use {}{}{}?",
                    name.italic().yellow(),
                    " = ".italic().yellow(),
                    "VALUE".italic().yellow(),
                )
            }

            CompilationError::UndefinedOperator(file, op) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Undefined operator ".bold(),
                    op.italic().bold(),
                    " .".bold()
                )
            }

            CompilationError::CannotMutate(file, name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Cannot mutate ".bold(),
                    name.italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::MismatchedTypeInDef(file, name, expected, got) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}{}{}{}",
                    "Mismatched type ".bold(),
                    got.to_string().italic().bold(),
                    "in ".bold(),
                    name.italic().bold(),
                    "; expected type ".bold(),
                    expected.to_string().italic().bold()
                )
            }

            CompilationError::UndefinedFunction(file, name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;
                writeln!(
                    f,
                    "    {}{}{}",
                    "Function ".bold(),
                    name.italic().bold(),
                    " is not defined.".bold()
                )?;
                write!(
                    f,
                    "{}{}{}{}",
                    "    Try adding ",
                    "fn ".italic().yellow(),
                    name.italic().yellow(),
                    "(ARGS) -> RET_TY".italic().yellow(),
                )
            }
        }
    }
}
