pub mod preopt;

use crate::parser::{AstNode, ParseBlock};
use std::ops::Deref;

pub use preopt::PreoptEngine;

#[derive(Debug, PartialEq, Clone)]
pub enum UsageKind {
    Assignment,
    Get,
    Call(Vec<AstNode>),
    Definition,
    MakePointer,
}

#[derive(Debug)]
pub struct UsageIntrinsic {
    pub name: String,
    pub kind: UsageKind,
}

impl UsageIntrinsic {
    pub fn new(name: String, kind: UsageKind) -> UsageIntrinsic {
        UsageIntrinsic { name, kind }
    }
}

pub fn get_usages_of(symbol: &String, code: &[AstNode]) -> Vec<UsageIntrinsic> {
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
            AstNode::PrefixOp(op, n)
                if &**op == "&" && n.deref() == &AstNode::Identifier(symbol.clone()) =>
            {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::MakePointer))
            }
            AstNode::PrefixOp(_, r) => usages.extend(get_usages_of(symbol, &[r.deref().clone()])),
            AstNode::PostfixOp(l, _) => usages.extend(get_usages_of(symbol, &[l.deref().clone()])),
            AstNode::MemberExpr(c) if c[0] == *symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Get))
            }
            AstNode::IdxAccess(o, i) => {
                usages.extend(get_usages_of(symbol, &[o.deref().clone()]));
                usages.extend(get_usages_of(symbol, &[i.deref().clone()]));
            }
            AstNode::CallExpr { callee, args } => {
                if let AstNode::Identifier(name) = callee.deref() {
                    if name == symbol {
                        usages.push(UsageIntrinsic::new(
                            symbol.clone(),
                            UsageKind::Call(args.to_vec()),
                        ));
                    }
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
            AstNode::ForInStmt {
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
            AstNode::FnStmt {
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
            AstNode::MemberExpr(p) if p.contains(symbol) => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Get));
            }
            _ => continue,
        }
    }

    usages
}
