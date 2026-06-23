#![feature(int_from_ascii)]
#![feature(generic_atomic)]
#![feature(is_ascii_octdigit)]

use cranelift_codegen::settings;

pub mod cli;
pub mod file;
pub mod reader;
pub mod states;
pub mod utils;

fn _salj() {
    settings::detail::Template
}