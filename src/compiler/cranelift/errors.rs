use std::fmt::{write, Display};
use std::path::PathBuf;
use colored::Colorize;

pub enum CraneliftError {
    UnknownModule(PathBuf, Box<[String]>),
    UndefinedVariable(PathBuf, String),
    DualDefinition(PathBuf, String),
}

impl Display for CraneliftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CraneliftError::UnknownModule(file, modules) => {
                let module = modules.join("::");
                
                writeln!(f, "  {}{}", "Error in file ".bold().bright_red(), file.to_string_lossy().bold().bright_red())?;
                writeln!(f, "    {}{}{}", "Module ".bold(), module.italic().bold(), " not found.".bold())?;
                write!(
                    f, "{}{}{}{}{}{}{}",
                    "    Maybe you need to install a module via ",
                    "mosaic install ".italic().yellow(),
                    modules.first().unwrap().bold().italic().yellow(),
                    " or check ",
                    modules.first().unwrap().bold(),
                    "'s documentation at ",
                    format!("https://msc.ljpprojects.org/module/{}", modules.first().unwrap()).bold().italic().blue().underline()
                )
            }

            CraneliftError::UndefinedVariable(file, name) => {
                writeln!(f, "  {}{}", "Error in file ".bold().bright_red(), file.to_string_lossy().bold().bright_red())?;
                writeln!(f, "    {}{}{}", "Variable ".bold(), name.italic().bold(), " is not defined.".bold())?;
                write!(
                    f, "{}{}{}{}",
                    "    Try adding ",
                    "def auto ".italic().yellow(),
                    name.italic().yellow(),
                    " -> VALUE".italic().yellow(),
                )
            }

            CraneliftError::DualDefinition(file, name) => {
                writeln!(f, "  {}{}", "Error in file ".bold().bright_red(), file.to_string_lossy().bold().bright_red())?;
                writeln!(f, "    {}{}{}", "Attempted to define variable ".bold(), name.italic().bold(), " multiple times.".bold())?;
                write!(
                    f, "    Did you mean to use {}{}{}?",
                    name.italic().yellow(),
                    " = ".italic().yellow(),
                    "VALUE".italic().yellow(),
                )
            }
        }
    }
}