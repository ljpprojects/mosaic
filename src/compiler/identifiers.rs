use core::fmt;
use std::fmt::Display;

use crate::parser::AstNode;

pub struct StatementIdentifier {
    node: AstNode,
    instance_number: u64,
}

fn mangle_stmt_identifier(identifier: &StatementIdentifier) -> String {
    let node_identifier = match identifier.node {
        AstNode::ForInStmt { .. } => "fiter",
        AstNode::ForCondStmt { .. } => "fcond",
        AstNode::LetStmt { .. } => "cstnt",
        AstNode::MutStmt { .. } => "mtble",
        AstNode::FnStmt { .. } => "fndec",
        AstNode::ExternFn { .. } => "extfn",
        AstNode::WhileStmt { .. } => "while",
        AstNode::IfStmt { .. } => "ifstm",
        AstNode::DeferStmt(..) => "defer",
        AstNode::IncludeStmt(..) => "incld",
        AstNode::ReturnStmt(..) => "retst",
        AstNode::TypeAlias(..) => "typal",
        _ => unreachable!(),
    };

    format!("stmt_{}_{}", node_identifier, identifier.instance_number)
}

impl Display for StatementIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", mangle_stmt_identifier(self))
    }
}