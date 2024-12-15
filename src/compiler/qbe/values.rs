use crate::compiler::qbe::types::QbeType;
use crate::compiler::{Generator, Value};
use crate::utils::{Indirection, UseSparingly};
use std::fmt::Display;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub enum QbeValue<'a> {
    Integer(u64, QbeType<'a>),
    Float(f64, QbeType<'a>),
    Pointer(u64),
    FatPointer(u64, u32, QbeType<'a>),
    TerminatedSlice(u64, Indirection<QbeValue<'a>>, QbeType<'a>),
    Boolean(bool),
    Temporary(String, QbeType<'a>),
    Global(String, QbeType<'a>),
    NullVoid
}

impl Display for QbeValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl<'a> Value<'a> for QbeValue<'a> {
    type ValType = QbeType<'a>;
    
    fn get_type(&self) -> Self::ValType {
        match self {
            QbeValue::Integer(_, t) => t.clone(),
            QbeValue::Float(_, t) => t.clone(),
            QbeValue::Pointer(_) => QbeType::Integer64,
            QbeValue::FatPointer(_, _, t) => t.clone(),
            QbeValue::TerminatedSlice(_, _, t) => t.clone(),
            QbeValue::Boolean(_) => QbeType::Boolean,
            QbeValue::Temporary(_, t) => t.clone(),
            QbeValue::Global(_, t) => t.clone(),
            QbeValue::NullVoid => QbeType::NullVoid
        }
    }
    
    fn set_type(&mut self, ty: Self::ValType) -> UseSparingly<()> {
        match self {
            QbeValue::Integer(_, t) => *t = ty,
            QbeValue::Float(_, t) => *t = ty,
            QbeValue::FatPointer(_, _, t) => *t = ty,
            QbeValue::TerminatedSlice(_, _, t) => *t = ty,
            QbeValue::Temporary(_, t) => *t = ty,
            QbeValue::Global(_, t) => *t = ty,
            _ => ()
        };

        ().into()
    }

    fn byte(b: i8) -> Self {
        QbeValue::Integer(b as u64, QbeType::Integer8)
    }

    fn short(b: i16) -> Self {
        QbeValue::Integer(b as u64, QbeType::Integer16)
    }

    fn word(b: i32) -> Self {
        QbeValue::Integer(b as u64, QbeType::Integer32)
    }

    fn long(b: i64) -> Self {
        QbeValue::Integer(b as u64, QbeType::Integer64)
    }

    fn float(b: f32) -> Self {
        QbeValue::Float(b as f64, QbeType::Float32)
    }

    fn double(b: f64) -> Self {
        QbeValue::Float(b, QbeType::Float64)
    }
}

impl PartialEq for QbeValue<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (QbeValue::Integer(i, t), QbeValue::Integer(i2, t2)) => i == i2 && t == t2,
            (QbeValue::Float(f, t), QbeValue::Float(f2, t2)) => f == f2 && t == t2,
            (QbeValue::Pointer(a), QbeValue::Pointer(a2)) => a == a2,
            (QbeValue::FatPointer(a, l, t), QbeValue::FatPointer(a2, l2, t2)) => a == a2 && l == l2 && t == t2,
            (QbeValue::TerminatedSlice(a, e, t), QbeValue::TerminatedSlice(a2, e2, t2)) => a == a2 && e.deref() == e2.deref() && t == t2,
            (QbeValue::Boolean(b), QbeValue::Boolean(b2)) => b == b2,
            (QbeValue::Temporary(n, t), QbeValue::Temporary(n2, t2)) => n == n2 && t == t2,
            (QbeValue::Global(n, t), QbeValue::Global(n2, t2)) => n == n2 && t == t2,
            (QbeValue::NullVoid, QbeValue::NullVoid) => true,
            _ => false
        }
    }
}

impl<'a> QbeValue<'a> {
    pub fn into_qbe(self) -> qbe::Value {
        match self {
            QbeValue::Integer(i, _) => qbe::Value::Const(i),
            QbeValue::Float(f, _) => qbe::Value::Const(u64::from_be_bytes(f.to_be_bytes())),
            QbeValue::Pointer(a) => qbe::Value::Const(a),
            QbeValue::FatPointer(a, _, _) => qbe::Value::Const(a),
            QbeValue::TerminatedSlice(a, _, _) => qbe::Value::Const(a),
            QbeValue::Boolean(b) if b => qbe::Value::Const(1),
            QbeValue::Boolean(..) => qbe::Value::Const(0),
            QbeValue::NullVoid => qbe::Value::Const(0),
            QbeValue::Temporary(n, _) => qbe::Value::Temporary(n),
            QbeValue::Global(n, _) => qbe::Value::Global(n),
        }
    }
}