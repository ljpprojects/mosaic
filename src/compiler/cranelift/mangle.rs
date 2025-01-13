use std::ops::Deref;
use crate::compiler::cranelift::types::CraneliftType;

pub fn mangle_type(ty: &CraneliftType) -> String {
    match ty {
        CraneliftType::Generic(..) => ty.to_string(), // panics
        CraneliftType::Any => "A".into(),
        CraneliftType::Int8 => "c".into(),
        CraneliftType::Int16 => "s".into(),
        CraneliftType::Int32 => "w".into(),
        CraneliftType::Int64 => "l".into(),
        CraneliftType::UInt8 => "Uc".into(),
        CraneliftType::UInt16 => "Us".into(),
        CraneliftType::UInt32 => "Uw".into(),
        CraneliftType::UInt64 => "Ul".into(),
        CraneliftType::Float32 => "f".into(),
        CraneliftType::Float64 => "d".into(),
        CraneliftType::Null => "v".into(),
        CraneliftType::Bool => "b".into(),
        CraneliftType::FuncPtr { ret_type, arg_types } => format!("F{}_{ret_type}", arg_types.iter().map(|a| mangle_type(a)).collect::<Vec<_>>().join("_")),
        CraneliftType::CPtr(inner) => format!("P{}", mangle_type(inner)),
        CraneliftType::Slice(inner, len) => format!("S{}_{len}", mangle_type(inner)),
        CraneliftType::CStr => "Pc".into(),
        CraneliftType::UCStr => "PUc".into()
    }
}

pub fn mangle_function(name: &String, arg_types: &[CraneliftType], ret_type: &CraneliftType) -> String {
    if arg_types.len() != 0 {
        format!("F{L}{name}{}_{}", mangle_type(ret_type), arg_types.iter().map(|a| mangle_type(a)).collect::<Vec<_>>().join("_"), L = name.len())
    } else {
        format!("F{L}{name}{}", mangle_type(ret_type), L = name.len())
    }
}