pub mod preopt;

use crate::parser::{AstNode, ParseBlock};
use std::ops::Deref;

pub use preopt::PreoptEngine;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UsageKind {
    Assignment,
    Get,
    Call,
    Definition,
}

#[derive(Debug)]
struct UsageIntrinsic {
    pub name: String,
    pub kind: UsageKind,
}

impl UsageIntrinsic {
    pub fn new(name: String, kind: UsageKind) -> UsageIntrinsic {
        UsageIntrinsic { name, kind }
    }
}

fn get_usages_of(symbol: &String, code: &[AstNode]) -> Vec<UsageIntrinsic> {
    let mut usages = Vec::new();

    // We want to look through the following nodes:
    // - call expr
    // - identifier
    // - \w parse blocks
    // - assignments

    for node in code {
        match node {
            AstNode::ArrayLiteral(vals) => usages.extend(get_usages_of(symbol, vals)),
            AstNode::Identifier(i) if i == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Get))
            }
            AstNode::InfixOp(l, o, r) => {
                if &**o == "=" {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Assignment));
                    usages.extend(get_usages_of(symbol, &[r.deref().clone()]))
                } else {
                    usages.extend(get_usages_of(symbol, &[l.deref().clone()]));
                    usages.extend(get_usages_of(symbol, &[r.deref().clone()]))
                }
            }
            AstNode::PrefixOp(_, r) => usages.extend(get_usages_of(symbol, &[r.deref().clone()])),
            AstNode::PostfixOp(l, _) => usages.extend(get_usages_of(symbol, &[l.deref().clone()])),
            AstNode::MemberExpr(c) if c.first().unwrap() == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Get))
            }
            AstNode::IdxAccess(o, i) => {
                usages.extend(get_usages_of(symbol, &[o.deref().clone()]));
                usages.extend(get_usages_of(symbol, &[i.deref().clone()]));
            }
            AstNode::CallExpr { callee, args } => {
                if let AstNode::Identifier(name) = callee.deref()
                    && name == symbol
                {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Call));
                }

                usages.extend(get_usages_of(symbol, args));
            }
            AstNode::AsExpr(l, _) => usages.extend(get_usages_of(symbol, &[l.as_ref().clone()])),
            AstNode::IfExpr {
                cond,
                else_clause: ParseBlock::Plain(else_code),
                block: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));
                usages.extend(get_usages_of(symbol, code));
                usages.extend(get_usages_of(symbol, else_code));
            }
            AstNode::ForInExpr {
                var,
                of,
                block: ParseBlock::Plain(block),
            } => {
                if var == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                usages.extend(get_usages_of(symbol, &[of.deref().clone()]));
                usages.extend(get_usages_of(symbol, block));
            }
            AstNode::FnExpr {
                name,
                code: ParseBlock::Plain(code),
                ..
            } => {
                if name == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                usages.extend(get_usages_of(symbol, code));
            }
            AstNode::LetStmt { name, value, .. } | AstNode::MutStmt { name, value, .. } => {
                if name == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                usages.extend(get_usages_of(symbol, &[value.deref().clone()]));
            }
            AstNode::WhileStmt {
                cond,
                code: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));

                usages.extend(get_usages_of(symbol, code));
            }
            AstNode::StructStmt { name, fields, .. } => {
                if name == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                for (name, _) in fields {
                    if name == symbol {
                        usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                    }
                }
            }
            AstNode::IfStmt {
                cond,
                block: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));
                usages.extend(get_usages_of(symbol, code));
            }
            AstNode::ExternFn { name, .. } if name == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition))
            }
            AstNode::ExternDef { name, .. } if name == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition))
            }
            AstNode::ReturnStmt(v) => usages.extend(get_usages_of(symbol, &[v.as_ref().clone()])),
            AstNode::Macro(name, args) => {
                if name == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                usages.extend(get_usages_of(symbol, args));
            }
            _ => continue,
        }
    }

    usages
}