use crate::parser::{AstNode, ParseBlock};

/// Returns an ast where alkl code that *might* run is flattened (including if and match)
pub fn flatten_ast(nodes: &[AstNode]) -> Vec<AstNode> {
    let mut flattened = vec![];

    for node in nodes {
        flattened.push(node.clone()); // Push the node

        match node { // Push the flattened node
            AstNode::IfExpr {
                line_info: _,
                cond,
                block: ParseBlock::Plain(code),
                else_clause: ParseBlock::Plain(else_code),
            } => {
                flattened.extend(flatten_ast(&*code));
                flattened.extend(flatten_ast(&*else_code));
                flattened.push(cond.as_ref().clone());
            },

            AstNode::MatchExpr {
                line_info: _,
                matchee,
                arms,
            } => {
                flattened.extend(flatten_ast(&*arms.iter().map(|a| {
                    let ParseBlock::Plain(ref code) = a.code;

                    flatten_ast(&*code)
                }).flatten().collect::<Vec<_>>()));
                flattened.push(matchee.as_ref().clone());
            },

            // --- Statements and expressions at the same time? --- //

            AstNode::GuardClause {
                line_info: _,
                cond,
                else_code: ParseBlock::Plain(else_code),
            } => {
                flattened.extend(flatten_ast(&*else_code));
                flattened.push(cond.as_ref().clone());
            },

            // --- Statements --- //

            AstNode::AbortingAsExpr(_, v, _) | AstNode::AsExpr(_, v, _) => flattened.extend(flatten_ast(&[v.as_ref().clone()])),

            AstNode::ArrayLiteral(_, a) => flattened.extend(flatten_ast(&*a)),

            AstNode::CallExpr {
                line_info: _,
                callee,
                args
            } => {
                flattened.extend(flatten_ast(&*args));
                flattened.extend(flatten_ast(&[callee.as_ref().clone()]));
            },

            AstNode::DataInitExpr {
                name: _,
                fields,
                line_info: _,
            } => {
                flattened.extend(flatten_ast(&*fields.iter().map(|(_, v, )| flatten_ast(&[v.as_ref().clone()])).flatten().collect::<Vec<_>>()));
            },

            AstNode::IdxAccess(_, o, i) => {
                flattened.extend(flatten_ast(&[o.as_ref().clone()]));
                flattened.extend(flatten_ast(&[i.as_ref().clone()]));
            },

            AstNode::InfixOp(_, l, _, r) => {
                flattened.extend(flatten_ast(&[l.as_ref().clone()]));
                flattened.extend(flatten_ast(&[r.as_ref().clone()]));
            },

            AstNode::LetStmt { name_info: _, name: _, def_type: _, value } | AstNode::MutStmt { name_info: _, name: _, def_type: _, value } =>
                flattened.extend(flatten_ast(&[value.as_ref().clone()])),

            AstNode::PostfixOp(_, l, _) => flattened.extend(flatten_ast(&[l.as_ref().clone()])),

            AstNode::PrefixOp(_, _, r) => flattened.extend(flatten_ast(&[r.as_ref().clone()])),

            AstNode::ReturnStmt(_, v) => flattened.extend(flatten_ast(&[v.as_ref().clone()])),

            AstNode::ForInStmt {
                line_info: _,
                var: _,
                of,
                block: ParseBlock::Plain(code),
            } => {
                flattened.extend(flatten_ast(&*code));
                flattened.push(of.as_ref().clone());
            },

            AstNode::ForCondStmt {
                line_info: _,
                var: _,
                threshold: _,
                operator,
                block: ParseBlock::Plain(code),
            } => {
                flattened.extend(flatten_ast(&*code));
                flattened.push(operator.as_ref().clone());
            },

            AstNode::FnStmt {
                line_info: _,
                of: _,
                name: _,
                ret_type: _,
                args: _,
                type_generics: _,
                code: ParseBlock::Plain(code),
                modifiers: _,
            } => flattened.extend(flatten_ast(&*code)),

            AstNode::WhileStmt {
                line_info: _,
                cond,
                code: ParseBlock::Plain(code),
            } => {
                flattened.extend(flatten_ast(&*code));
                flattened.push(cond.as_ref().clone());
            },

            AstNode::IfStmt {
                line_info: _,
                cond,
                block: ParseBlock::Plain(code),
            } => {
                flattened.extend(flatten_ast(&*code));
                flattened.push(cond.as_ref().clone());
            },

            AstNode::DeferStmt(_, ParseBlock::Plain(code)) => flattened.extend(flatten_ast(&*code)),

            n => flattened.push(n.clone()),
        }
    }

    flattened
}
