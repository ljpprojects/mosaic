use crate::compiler::cranelift::meta::MustFreeMeta;
use crate::parser::{AstNode, MacroArgKind, ParseType};
use crate::tokens::{LineInfo, Token};
use colored::Colorize;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;
use std::rc::Rc;
use either::Either;
use crate::compiler::cranelift::trace::Trace;
use crate::compiler::traits::CompilationType;

#[derive(Clone)]
pub enum CompilationError {
    /**** Lex errors ****/
    InvalidChar(PathBuf, char, LineInfo),
    UnfinishedString(PathBuf, LineInfo),
    TooManyLines(PathBuf),

    /**** Parse errors ****/
    ExpectedToken(PathBuf, Token, Token),
    UnexpectedEOF(PathBuf, String),
    InvalidNode(PathBuf, AstNode),
    InvalidToken(PathBuf, Token),
    Forbidden(PathBuf, String),
    UnknownNodeType(PathBuf, String, String),
    UndefinedMacro(PathBuf, String),
    InvalidMacroArg {
        file: PathBuf,
        arg_idx: usize,
        arg_name: String,
        expected: MacroArgKind,
        macro_name: String,
        got_node: Either<AstNode, ParseType>,
    },

    /**** Compilation errors ****/
    UnknownModule(PathBuf, Trace, Box<[String]>),
    UndefinedVariable(PathBuf, Trace, String),
    DualDefinition(PathBuf, Trace, String),
    UndefinedOperator(PathBuf, Trace, String),
    MismatchedTypeInDef(PathBuf, Trace, String, Rc<dyn CompilationType>, Rc<dyn CompilationType>),
    CannotMutate(PathBuf, Trace, String),
    UndefinedFunction(PathBuf, Trace, String),
    InvalidCast(PathBuf, Trace, Rc<dyn CompilationType>, Rc<dyn CompilationType>),
    CannotMakePointer(PathBuf, Trace, String),
    NotFreed(PathBuf, Trace, MustFreeMeta),
    InvalidSignature(PathBuf, Trace, String, Rc<dyn CompilationType>, Vec<Rc<dyn CompilationType>>)
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
                write!(
                    f,
                    "    {}{}{}",
                    "Unexpected EOF; expected token ".bold(),
                    format!("{expected:?}").italic().bold(),
                    ".".bold()
                )
            }
            
            CompilationError::UnknownNodeType(file, macro_name, node_type) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                write!(
                    f,
                    "    {}{}{}{}{}",
                    "Invalid node type ".bold(),
                    node_type.italic().bold(),
                    " in macro ".bold(),
                    macro_name.italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::UndefinedMacro(file, macro_name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                write!(
                    f,
                    "    {}{}{}",
                    "Undefined macro ".bold(),
                    macro_name.italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::InvalidMacroArg {
                file, arg_idx, arg_name, expected, macro_name, got_node
            } => {
                writeln!(
                    f,
                    "  {}{}",
                    "Parsing error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                writeln!(
                    f,
                    "    {}{}{}{}{}{}{}",
                    "Invalid macro argument for ".bold(),
                    macro_name.italic().bold(),
                    " at index ".bold(),
                    arg_idx.to_string().italic().bold(),
                    " (".bold(),
                    arg_name.italic().bold(),
                    ").".bold(),
                )?;

                write!(
                    f,
                    "{}{}{}{}.",
                    "Expected a node matching ",
                    expected.to_string().italic(),
                    ", but got ",
                    got_node.to_string().italic()
                )
            }

            CompilationError::UnknownModule(file, trace, modules) => {
                let module = modules.join("::");

                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                let Ok(home) = std::env::var("HOME") else {
                    panic!("Expected a HOME variable.")
                };
                
                let Some(tmp) = modules.as_ref().split_last() else {
                    unreachable!()
                };
                
                let search_path = tmp.1.join("/");

                writeln!(
                    f,
                    "    {}{}{}{}",
                    "Module ".bold(),
                    module.italic().bold(),
                    " not found.".bold(),
                    format!(
                        "{home}/.msc/mods/{search_path}/{}.msc",
                        modules[0]
                    )
                )?;
                write!(
                    f,
                    "{}{}{}{}{}{}{}",
                    "    Maybe you need to install a module via ",
                    "mosaic install ".italic().yellow(),
                    modules[0].bold().italic().yellow(),
                    " or check ",
                    modules[0].bold(),
                    "'s documentation at ",
                    format!(
                        "https://msc.ljpprojects.org/module/{}",
                        modules[0]
                    )
                    .bold()
                    .italic()
                    .blue()
                    .underline()
                )
            }

            CompilationError::UndefinedVariable(file, trace, name) => {
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
                    "let ".italic().yellow(),
                    name.italic().yellow(),
                    ": TYPE = VALUE".italic().yellow(),
                )
            }

            CompilationError::DualDefinition(file, trace, name) => {
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

            CompilationError::UndefinedOperator(file, trace, op) => {
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

            CompilationError::CannotMutate(file, trace, name) => {
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

            CompilationError::MismatchedTypeInDef(file, trace, name, expected, got) => {
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

            CompilationError::UndefinedFunction(file, trace, name) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                writeln!(f, "{trace:#?}")?;

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

            CompilationError::InvalidCast(file, trace, from, to) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                write!(
                    f,
                    "{}{}{}{}{}",
                    "Invalid cast from type ".bold(),
                    from.to_string().italic().bold(),
                    " to ".bold(),
                    to.to_string().italic().bold(),
                    ".".bold()
                )
            }

            CompilationError::CannotMakePointer(file, trace, to) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                writeln!(
                    f,
                    "{}{}{}",
                    "Attempted to create a pointer (which is alwyas mutable) to an immutable variable ".bold(),
                    to.to_string().italic().bold(),
                    ".".bold()
                )?;

                write!(
                    f,
                    "{}{}{}{}{}{}",
                    "    Try changing ",
                    to.to_string().italic().bold(),
                    "'s definition to: ".bold(),
                    "mut ".italic().yellow(),
                    to.italic().yellow(),
                    ": TYPE = VAL".italic().yellow(),
                )
            }

            CompilationError::NotFreed(file, trace, item) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                writeln!(
                    f,
                    "{}{}{}",
                    "Value returned from function ".bold(),
                    item.returned_from.italic().bold(),
                    " was not freed.".bold()
                )?;

                write!(
                    f,
                    "{}{}{}",
                    "Note: Required value to be freed because of explicit ",
                    "must_free ".italic(),
                    "modifier."
                )
            }

            CompilationError::InvalidSignature(file, trace, name, ret, args) => {
                writeln!(
                    f,
                    "  {}{}",
                    "Compilation error in file ".bold().bright_red(),
                    file.to_string_lossy().bold().bright_red()
                )?;

                write!(
                    f,
                    "{}{}{}{}{}{}{}{}",
                    "Invalid signature `".bold(),
                    "fn(".italic().bold(),
                    args.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", ").italic().bold(),
                    ") -> ".italic().bold(),
                    ret.to_string().italic().bold(),
                    "` for function ".bold(),
                    name.italic().bold(),
                    ".".bold()
                )
            }
        }
    }
}