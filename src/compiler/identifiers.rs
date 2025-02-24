use std::fmt::Display;

use crate::parser::AstNode;

pub struct StatementIdentifier {
    node: AstNode,
    instance_number: u64,
}

fn mangle_stmt_identifier(identifier: StatementIdentifier) -> String {
    format!("stmt_")
}

impl Display for StatementIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "")
    }
}