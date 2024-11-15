use crate::parser::AstNode;
use crate::runtime::types::Type;
use crate::runtime::values::{ReprBool, ReprString, RuntimeValue};
use crate::scope::Scope;

pub fn eval<'a>(scope: &mut Scope <'a>, stmt: &AstNode) -> RuntimeValue<'a> {
    match stmt {
        AstNode::NumberLiteral(_) | AstNode::StringLiteral(_) | AstNode::BooleanLiteral(_) | AstNode::NullLiteral => eval_literal_expr(stmt),
        AstNode::DefStmt { .. } => eval_def_stmt(scope, stmt),
        _ => unimplemented!("Evaluate node {stmt:?}")
    }
}

pub fn eval_literal_expr<'a>(expr: &AstNode) -> RuntimeValue<'a> {
    match expr {
        AstNode::NumberLiteral(n) => if n.fract() == 0f64 {
            RuntimeValue::Integer((*n as i64).to_be_bytes())
        } else {
            RuntimeValue::Float(n.to_be_bytes())
        },
        AstNode::StringLiteral(s) => {
            let repr = ReprString(s.clone().into_bytes().into_boxed_slice());
            RuntimeValue::String(repr)
        },
        AstNode::NullLiteral => RuntimeValue::Null,
        AstNode::BooleanLiteral(b) => RuntimeValue::Bool(ReprBool(*b)),
        _ => unreachable!()
    }   
}

pub fn eval_def_stmt<'a>(scope: &mut Scope<'a>, stmt: &AstNode) -> RuntimeValue<'a> {
    let AstNode::DefStmt { name, def_type, value } = stmt else { unreachable!() };
    
    let value = eval(scope, value);
    
    scope.set_var(&name, value, Type::Any);
    
    RuntimeValue::Null
}