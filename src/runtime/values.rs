use std::collections::HashMap;
use std::fmt::Debug;
use crate::runtime::types::Type;

type ReprByte = u8;
type ReprAddress = usize;

trait ReprBinary: Clone {}

#[derive(Clone)]
pub(crate) struct ReprString(pub(crate) Box<[ReprByte]>);

impl Debug for ReprString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = String::from_utf8(self.0.to_vec()).unwrap();
        write!(f, "\"{}\"", s)
    }
}

#[derive(Clone, Debug)]
pub struct ReprBool(pub bool);

#[derive(Clone)]
pub struct ReprBorrow<'a>(pub ReprAddress, pub Type<'a>);

#[derive(Clone)]
pub struct ReprBorrowMut<'a>(pub ReprAddress, pub Type<'a>);

#[derive(Debug)]
struct ReprObject<'a> {
    entry_count: [ReprByte; 2],
    entries: &'a [RuntimeValue<'a>],
    mutable: ReprBool
}

#[derive(Clone)]
struct ReprPointer(ReprAddress);

impl ReprBinary for ReprBool {}
impl ReprBinary for ReprString {}
impl ReprBinary for ReprBorrow<'_> {}
impl ReprBinary for ReprBorrowMut<'_> {}
impl ReprBinary for ReprObject<'_> {}

impl Clone for ReprObject<'_> {
    fn clone(&self) -> Self {
        Self {
            entry_count: self.entry_count.clone(),
            entries: self.entries.clone(),
            mutable: self.mutable.clone()
        }
    }
}

impl ReprObject<'_> {
    fn from_hashmap(map: HashMap<String, RuntimeValue>, mutable: bool) -> Self {
        let entry_count = map.len();
        
        Self {
            entry_count: (entry_count as u16).to_le_bytes().into(),
            mutable: ReprBool(mutable),
            entries: &[]
        }
    }
}

#[derive(Clone)]
pub enum RuntimeValue<'a> {
    /// Used in code as simply 'null'
    /// This is not a basic type, and doesn't support processing
    Null,
    
    /// Used in code as ibasic of std::internal
    Integer([ReprByte; 8]),

    /// Used in code as fbasic of std::internal
    Float([ReprByte; 8]),

    /// Used in code as sbasic of std::internal
    String(ReprString),
    
    /// Used in code as obasic of std::internal
    Object(ReprObject<'a>),
    
    /// Used in code as boolbasic of std::internal
    Bool(ReprBool),
    
    Borrow(ReprBorrow<'a>),
    BorrowMut(ReprBorrowMut<'a>),
}

impl Debug for RuntimeValue<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RuntimeValue::Null => write!(f, "null"),
            RuntimeValue::Integer(bytes) => write!(f, "{}", i64::from_be_bytes(*bytes)),
            RuntimeValue::Float(bytes) => write!(f, "{}", f64::from_be_bytes(*bytes)),
            RuntimeValue::String(string) => write!(f, "{:?}", string),
            RuntimeValue::Bool(b) => write!(f, "{b:?}"),
            _ => Err(std::fmt::Error),
        }
    }
}