use crate::parser::{AstNode, ParseBlock};
use std::ops::Deref;

#[derive(Debug, PartialEq, Clone)]
pub enum UsageKind {
    Assignment,
    Get,
    Call(Vec<AstNode>),
    Definition,
    MakePointer,
    Instantiate,
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
    // - returns

    for node in code {
        match node {
            AstNode::ArrayLiteral(_, vals) => usages.extend(get_usages_of(symbol, vals)),
            AstNode::Identifier(_, i) if i == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Get))
            }
            AstNode::Identifier(..) => continue,
            AstNode::InfixOp(_, l, o, r) => {
                if &**o == "=" {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Assignment));
                    usages.extend(get_usages_of(symbol, &[r.deref().clone()]))
                } else {
                    usages.extend(get_usages_of(symbol, &[l.deref().clone()]));
                    usages.extend(get_usages_of(symbol, &[r.deref().clone()]))
                }
            }
            AstNode::PrefixOp(_, op, n)
                if &**op == "&" && matches!(&**n, AstNode::Identifier(_, nm) if nm.clone() == symbol.clone()) =>
            {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::MakePointer))
            }
            AstNode::PrefixOp(_, _, r) => usages.extend(get_usages_of(symbol, &[r.deref().clone()])),
            AstNode::PostfixOp(_, l, _) => usages.extend(get_usages_of(symbol, &[l.deref().clone()])),
            AstNode::MemberExpr(_, r, _) => {
                usages.extend(get_usages_of(symbol, &[r.as_ref().clone()]))
            }
            AstNode::MemberExpr(..) => continue,
            AstNode::IdxAccess(_, o, i) => {
                usages.extend(get_usages_of(symbol, &[o.deref().clone()]));
                usages.extend(get_usages_of(symbol, &[i.deref().clone()]));
            }
            AstNode::CallExpr { line_info: _, callee, args } => {
                if let AstNode::Identifier(_, name) = callee.deref() {
                    if name == symbol {
                        usages.push(UsageIntrinsic::new(
                            symbol.clone(),
                            UsageKind::Call(args.to_vec()),
                        ));
                    }
                }

                usages.extend(get_usages_of(symbol, args));
            }
            AstNode::AbortingAsExpr(_, v, _) | AstNode::AsExpr(_, v, _) => usages.extend(get_usages_of(symbol, &[v.as_ref().clone()])),
            AstNode::IfExpr {
                line_info: _,
                cond,
                else_clause: ParseBlock::Plain(else_code),
                block: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));
                usages.extend(get_usages_of(symbol, code));
                usages.extend(get_usages_of(symbol, else_code));
            }
            AstNode::ForInStmt {
                line_info: _,
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
                line_info: _,
                cond,
                code: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));

                usages.extend(get_usages_of(symbol, code));
            }
            AstNode::IfStmt {
                line_info: _,
                cond,
                block: ParseBlock::Plain(code),
            } => {
                usages.extend(get_usages_of(symbol, &[cond.deref().clone()]));
                usages.extend(get_usages_of(symbol, code));
            }
            AstNode::ExternFn { name, .. } if name == symbol => {
                usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition))
            }
            AstNode::ExternFn { .. } => continue,
            AstNode::ReturnStmt(_, v) => usages.extend(get_usages_of(symbol, &[v.as_ref().clone()])),
            AstNode::MatchExpr {
                line_info: _,
                matchee,
                arms,
            } => {
                usages.extend(get_usages_of(symbol, &*arms.iter().map(|a| {
                    let ParseBlock::Plain(ref code) = a.code;

                    (&*code).clone()
                }).flatten().collect::<Vec<_>>()));
                usages.extend(get_usages_of(symbol, &[matchee.as_ref().clone()]));
            },

            // --- Statements and expressions at the same time? --- //

            AstNode::GuardClause {
                line_info: _,
                cond,
                else_code: ParseBlock::Plain(else_code),
            } => {
                usages.extend(get_usages_of(symbol, &*else_code));
                usages.extend(get_usages_of(symbol, &[cond.as_ref().clone()]));
            },

            // --- Statements --- //

            AstNode::DataInitExpr {
                name,
                fields,
                line_info: _,
            } => {
                if name == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Instantiate));
                }

                usages.extend(get_usages_of(symbol, &*fields.iter().map(|(_, v, )| v.as_ref().clone()).collect::<Vec<_>>()));
            },

            AstNode::ForCondStmt {
                line_info: _,
                var,
                threshold: _,
                operator,
                block: ParseBlock::Plain(code),
            } => {
                if var == symbol {
                    usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition));
                }

                usages.extend(get_usages_of(symbol, &*code));
                usages.extend(get_usages_of(symbol, &[operator.as_ref().clone()]));
            },

            AstNode::DeferStmt(_, ParseBlock::Plain(code)) => usages.extend(get_usages_of(symbol, &*code)),

            AstNode::TypeAlias(_, nm, _) if nm == symbol => usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition)),
            AstNode::TypeAlias(..) => continue,

            AstNode::DataStmt {
                name,
                ..
            } if name == symbol => usages.push(UsageIntrinsic::new(symbol.clone(), UsageKind::Definition)),
            AstNode::DataStmt { .. } => continue,

            AstNode::ByteLiteral(..) | AstNode::BooleanLiteral(..) | AstNode::NullLiteral(..) | AstNode::StringLiteral(..) | AstNode::NumberLiteral(..) | AstNode::Path(..) | AstNode::SizeOf(..) | AstNode::IncludeStmt(..) | AstNode::MacroUseArg(..) | AstNode::BreakStmt(_) => continue,
        }
    }

    usages
}
