pub mod errors;
pub mod mangler;
pub mod types;
pub mod values;
pub mod linker;
pub mod modules;

use crate::compiler::qbe::errors::{QbeGenerationError, QbeGenerationResult};
use crate::compiler::qbe::modules::QbeModule;
use crate::compiler::qbe::types::QbeType::Integer64;
use crate::compiler::qbe::types::TypeGenerator;
use crate::compiler::qbe::types::{QbeType, CSTRING_TYPES};
use crate::compiler::qbe::values::QbeValue;
use crate::compiler::{GeneratedModule, Generator, Mangle, Value, ValueType};
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, ParseBlock, ParseType, StreamedParser, TypeBound};
use crate::reader::CharReader;
use crate::utils::Indirection;
use qbe::{Cmp, DataDef, DataItem, Function, Instr, Linkage, Module, TypeDef};
use std::cell::{Cell, RefCell};
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fs;
use std::hash::Hash;
use std::ops::Deref;
use std::path::PathBuf;
use std::str::FromStr;

type ArgMeta<'a> = (String, QbeType<'a>, Option<QbeValue<'a>>);
type FunctionMeta<'a> = (QbeType<'a>, Vec<(String, Box<[ArgMeta<'a>]>)>);

#[derive(Debug, Clone, PartialEq)]
/// Generates code from many [AstNodes](AstNode)
pub struct QbeGenerator<'a> {
    file_path: PathBuf,
    associated_obj_path: Option<PathBuf>,
    
    /// A counter to provide unique names
    unique_name_counter: u32,
    module: Module<'a>,
    types: HashMap<String, QbeType<'a>>,
    scopes: Vec<HashMap<String, QbeValue<'a>>>,
    functions: HashMap<String, FunctionMeta<'a>>,
    datadefs: Vec<DataDef<'a>>,
    parser: StreamedParser,
    included_modules: Vec<QbeModule<'a>>,
    typedefs: Vec<TypeDef<'a>>,
}

impl<'a> Generator<'a> for QbeGenerator<'a> {
    fn generate(&'a mut self) -> QbeGenerationResult<QbeModule<'a>> {
        self.generate_global_stmt()?;
        
        let mut self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
        
        for module in self_cell.borrow().included_modules.iter() {
            self_cell.borrow_mut().datadefs.extend(module.datadefs.clone());
            self_cell.borrow_mut().typedefs.extend(module.typedefs.clone());
            self_cell.borrow_mut().functions.extend(module.functions.clone());
            
            for (n, f) in module.clone().functions.into_iter() {
                self_cell.borrow_mut().functions.insert(n, f);
            }
        }

        for def in self_cell.borrow().datadefs.iter() {
            self_cell.borrow_mut().module.add_data(def.clone());
        }

        for def in self_cell.borrow().typedefs.iter() {
            self_cell.borrow_mut().module.add_type(def.clone());
        }

        let mut name = self_cell.borrow().file_path.clone();
        name.set_extension("");

        let module = QbeModule::new(
            name.to_str().unwrap().to_string(),
            self_cell.borrow().module.clone(),
            self_cell.borrow().file_path.clone(),
            vec![],
            self_cell.borrow().included_modules.clone(),
            self_cell.borrow().typedefs.clone(),
            self_cell.borrow().functions.clone(),
            self_cell.borrow().datadefs.clone()
        );

        Ok(module)
    }

    fn generate_expr(
        &'a mut self,
        expr: AstNode,
        func: &mut Function<'a>,
    ) -> QbeGenerationResult<'a, QbeValue<'a>> {
        match expr {
            AstNode::ForInExpr { var, of, block } => {
                let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
                
                let of = unsafe { (self as *mut Self).as_mut().unwrap() }.generate_expr(of.deref().clone(), func)?;
                let ty = of.get_type();
                
                self_cell.borrow_mut().unique_name_counter += 1;

                let cond_label = format!("for.in.{C}.cond", C = self_cell.borrow().unique_name_counter);
                let body_label = format!("for.in.{C}.body", C = self_cell.borrow().unique_name_counter);
                let end_label = format!("for.in.{C}.end", C = self_cell.borrow().unique_name_counter);

                let mut borrowed = self_cell.borrow_mut();
                let counter = (*borrowed).generate_temp(Integer64);

                func.assign_instr(
                    counter.clone().into_qbe(),
                    Integer64.into_qbe(false),
                    Instr::Copy(QbeValue::Pointer(0).into_qbe())
                );

                if !ty.iterable() {
                    return Err(QbeGenerationError::CannotIterate(Indirection::from(ty)))
                }

                func.add_block(cond_label.clone());

                let ty = match ty {
                    QbeType::Aggregate(_, i) => i.deref().clone(),
                    t => t,
                };

                let inner = match ty {
                    QbeType::FatPointer(ref i, _) | QbeType::Pointer(ref i) | QbeType::TerminatedSlice(ref i, _) => i.deref().clone(),
                    _ => unreachable!(),
                };

                match ty {
                    QbeType::FatPointer(_, l) => {
                        let mut borrowed = self_cell.borrow_mut();
                        let should_break = (*borrowed).generate_temp(QbeType::Boolean);

                        func.assign_instr(
                            should_break.clone().into_qbe(),
                            QbeType::Boolean.into_qbe(false),
                            Instr::Cmp(Integer64.into_qbe(false), Cmp::Slt, counter.clone().into_qbe(), QbeValue::Integer(l as u64, QbeType::Integer64).into_qbe()),
                        );

                        func.add_instr(Instr::Jnz(should_break.into_qbe(), body_label.clone(), end_label.clone()));
                    },
                    _ => todo!()
                }

                func.add_block(body_label);

                let mut borrowed = self_cell.borrow_mut();
                let addr = (*borrowed).generate_temp(Integer64);

                let mut borrowed = self_cell.borrow_mut();
                let offset = (*borrowed).generate_temp(Integer64);

                func.assign_instr(
                    offset.clone().into_qbe(),
                    Integer64.into_qbe(false),
                    Instr::Mul(counter.clone().into_qbe(), QbeValue::Integer(inner.clone().into_qbe(true).size(), QbeType::Integer64).into_qbe()),
                );

                func.assign_instr(
                    addr.clone().into_qbe(),
                    Integer64.into_qbe(false),
                    Instr::Add(of.into_qbe(), offset.into_qbe()),
                );

                let qbe_inner = inner.clone().into_qbe(true);

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let tmp = self2.declare_var(inner, var)?;

                func.assign_instr(tmp.into_qbe(), qbe_inner.clone(), Instr::Load(qbe_inner, addr.into_qbe()));

                let ParseBlock::Plain(block) = block;

                let mut result_values: Vec<QbeValue> = vec![];

                for (i, stmt) in block.iter().enumerate() {
                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };

                    if i == block.len() - 1 {
                        result_values.push(self2.generate_expr(stmt.clone(), func)?);
                    } else {
                        self2.generate_expr(stmt.clone(), func)?;
                    }
                }

                func.assign_instr(
                    counter.clone().into_qbe(),
                    Integer64.into_qbe(false),
                    Instr::Add(counter.into_qbe(), QbeValue::Integer(1, QbeType::Integer64).into_qbe()),
                );

                func.add_instr(Instr::Jmp(cond_label));

                func.add_block(end_label);

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                Ok(self2.generate_array_from_value_pairs(func, result_values.len() as u32, result_values.into_boxed_slice())?)
            }
            AstNode::InfixOp(left, op, right) => {
                self.generate_bin_op(left.deref().clone(), op, right.deref().clone(), func)
            }
            AstNode::NumberLiteral(_)
            | AstNode::StringLiteral(_)
            | AstNode::BooleanLiteral(_)
            | AstNode::NullLiteral
            | AstNode::Identifier(_) => self.generate_independent_expr(expr),
            AstNode::AsExpr(left, to) => {
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let left = self2.generate_expr(left.as_ref().clone(), func)?;
                let ty = left.get_type();

                let to = TypeGenerator::generate_type(to, unsafe { (self as *mut Self).as_mut().unwrap() }, &HashMap::new())?;

                match ty {
                    Integer64 | QbeType::Integer32 => {
                        match to {
                            QbeType::Integer8 => {
                                let tmp = self.generate_temp(QbeType::Integer8);

                                func.assign_instr(
                                    tmp.clone().into_qbe(),
                                    QbeType::Integer8.into_qbe_abi(),
                                    Instr::Copy(left.into_qbe()),
                                );

                                Ok(tmp)
                            },
                            t => Err(QbeGenerationError::InvalidCast(ty, t))
                        }
                    },
                    QbeType::FatPointer(_, _) => {
                        match to {
                            // converting *L[i8] to *i8
                            QbeType::Pointer(t) if matches!(t.deref(), QbeType::Integer8) => {
                                let QbeValue::Global(name, _) = left else {
                                    unreachable!()
                                };

                                let matched = self
                                    .datadefs
                                    .iter()
                                    .filter(|d| d.name == name)
                                    .collect::<Vec<&DataDef>>();
                                let def = matched.first().unwrap();

                                self.unique_name_counter += 1;

                                let name = format!("string.{C}", C = self.unique_name_counter);

                                let mut def = DataDef {
                                    linkage: Linkage::private(),
                                    name: name.clone(),
                                    align: None,
                                    items: def.items.clone(),
                                };

                                def.items
                                    .push((QbeType::Integer8.into_qbe_abi(), DataItem::Const(0)));

                                self.datadefs.push(def);

                                Ok(QbeValue::Global(name, QbeType::Pointer(t)))
                            }
                            // converting *L[i8] to *:0[i8]
                            QbeType::TerminatedSlice(t, e)
                            if matches!(t.deref(), QbeType::Integer8) && e.deref().clone() == QbeValue::Integer(0, QbeType::Integer8) =>
                                {
                                    let QbeValue::Global(name, _) = left else {
                                        unreachable!()
                                    };

                                    let matched = self
                                        .datadefs
                                        .iter()
                                        .filter(|d| d.name == name)
                                        .collect::<Vec<&DataDef>>();
                                    let def = matched.first().unwrap();

                                    self.unique_name_counter += 1;

                                    let name = format!("string.{C}", C = self.unique_name_counter);

                                    let mut def = DataDef {
                                        linkage: Linkage::private(),
                                        name: name.clone(),
                                        align: None,
                                        items: def.items.clone(),
                                    };

                                    def.items
                                        .push((QbeType::Integer8.into_qbe_abi(), DataItem::Const(0)));

                                    self.datadefs.push(def);

                                    let ty = QbeType::TerminatedSlice(t, e);

                                    Ok(QbeValue::Global(name, ty))
                                }
                            t => Err(QbeGenerationError::InvalidCast(ty, t)),
                        }
                    }
                    // converting *:0[i8] to *i8
                    QbeType::TerminatedSlice(_, e) if e.deref().clone() == QbeValue::Integer(0, QbeType::Integer8) => {
                        let QbeValue::TerminatedSlice(p, ..) = left else {
                            unreachable!()
                        };

                        Ok(QbeValue::Pointer(p))
                    }
                    t => Err(QbeGenerationError::InvalidCast(t, to)),
                }
            }
            AstNode::ArrayLiteral(els) => self.generate_array(func, els.len() as u32, els),
            AstNode::PrefixOp(_, _) => todo!(),
            AstNode::PostfixOp(_, _) => todo!(),
            AstNode::MemberExpr(_) => todo!(),
            AstNode::IdxAccess(left, i) => {
                let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
                
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let i = self2.generate_expr(i.deref().clone(), func)?;

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let left = self2.generate_expr(left.deref().clone(), func)?;
                let ty = left.get_type();

                let ty = match ty {
                    QbeType::Aggregate(_, i) => i.deref().clone(),
                    t => t
                };

                match ty {
                    QbeType::Pointer(inner) | QbeType::FatPointer(inner, _) => {
                        let mut borrowed = self_cell.borrow_mut();
                        let addr = (*borrowed).generate_temp(Integer64);

                        let mut borrowed = self_cell.borrow_mut();
                        let offset = (*borrowed).generate_temp(Integer64);

                        func.assign_instr(
                            offset.clone().into_qbe(),
                            Integer64.into_qbe(false),
                            Instr::Mul(i.into_qbe(), QbeValue::long(inner.deref().clone().into_qbe(false).size() as i64).into_qbe())
                        );

                        func.assign_instr(
                            addr.clone().into_qbe(),
                            Integer64.into_qbe(false),
                            Instr::Add(left.into_qbe(), offset.into_qbe()),
                        );

                        let loaded = self.generate_temp(inner.deref().clone());

                        let qbe_inner = inner.deref().clone().into_qbe(true);

                        func.assign_instr(
                            loaded.clone().into_qbe(),
                            qbe_inner.clone(),
                            Instr::Load(qbe_inner.clone(), addr.into_qbe()),
                        );

                        Ok(loaded)
                    },
                    t => Err(QbeGenerationError::CannotIndex(t))
                }
            }
            AstNode::CallExpr { callee, args } => {
                let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
                
                let mut new_args: Vec<(qbe::Type, qbe::Value)> = Vec::new();
                let mut comp_args: Vec<(QbeType, QbeValue)> = Vec::new();

                for arg in args.iter() {
                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    let v = self2.generate_expr(arg.clone(), func)?;
                    let ty = v.get_type();

                    comp_args.push((ty.clone(), v.clone()));
                    new_args.push((ty.into_qbe_abi(), v.into_qbe()));
                }

                let AstNode::Identifier(name) = callee.as_ref().clone() else {
                    todo!("Implement member-expression calls")
                };

                let borrowed = self_cell.borrow();
                let Some((ret_type, f)) = (*borrowed).functions.get(&name) else {
                    return Err(QbeGenerationError::UndefinedSymbol(name.clone()));
                };

                let arg_types = comp_args.iter().map(|(t, _)| t.clone()).collect::<Vec<_>>();

                println!("{arg_types:?}\n{f:?}");

                let (should_call, _) = f.iter().filter(|(_, a)| arg_types == a.iter().map(|(_, ty, _)| ty.clone()).collect::<Vec<_>>()).collect::<Vec<_>>().first().unwrap().clone();

                let tmp = self.generate_temp(ret_type.clone());

                func.assign_instr(
                    tmp.clone().into_qbe(),
                    ret_type.clone().into_qbe_abi(),
                    Instr::Call(should_call.clone(), new_args),
                );

                Ok(tmp)
            }
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
            } => {
                let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });

                let mut borrowed = self_cell.borrow_mut();
                (*borrowed).unique_name_counter += 1;

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let cond = self2.generate_expr(cond.deref().clone(), func)?;

                let if_label = format!("cond.if.{C}", C = (*borrowed).unique_name_counter);
                let else_label = format!("cond.else.{C}", C = (*borrowed).unique_name_counter);
                let end_label = format!("cond.end.{C}", C = (*borrowed).unique_name_counter);

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let mut result = self2.generate_temp(QbeType::NullVoid);
                let mut result_type = QbeType::Integer8;

                func.add_instr(Instr::Jnz(cond.into_qbe(), if_label.clone(), else_label.clone()));

                func.add_block(else_label);

                let ParseBlock::Plain(else_clause) = else_clause;

                for (i, stmt) in else_clause.iter().enumerate() {
                    if i == else_clause.len() - 1 {
                        let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                        let r = self2.generate_expr(stmt.clone(), func)?;
                        let ty = r.get_type();

                        result_type = ty.clone();

                        func.assign_instr(result.clone().into_qbe(), ty.into_qbe_abi(), Instr::Copy(r.into_qbe()));

                        break;
                    }

                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    self2.generate_expr(stmt.clone(), func)?;
                }

                func.add_instr(Instr::Jmp(end_label.clone()));

                func.add_block(if_label);

                let ParseBlock::Plain(block) = block;

                for (i, stmt) in block.iter().enumerate() {
                    if i == block.len() - 1 {
                        let r = self.generate_expr(stmt.clone(), func)?;
                        let ty = r.get_type();

                        result_type = ty.clone();

                        func.assign_instr(result.clone().into_qbe(), ty.into_qbe_abi(), Instr::Copy(r.into_qbe()));

                        break;
                    }

                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    self2.generate_expr(stmt.clone(), func)?;
                }

                func.add_block(end_label);

                result.set_type(result_type).acknowledge();

                Ok(result)
            }
            stmt => {
                self.generate_stmt(stmt, func)?;

                Ok(QbeValue::byte(0))
            }
        }
    }

    fn types(&self) -> HashMap<String, QbeType<'a>> {
        self.types.clone()
    }
}

impl<'a> QbeGenerator<'a> {
    fn generate_temp(&mut self, ty: QbeType<'a>) -> QbeValue {
        self.unique_name_counter += 1;
        QbeValue::Temporary(format!("tmp.{}", self.unique_name_counter), ty)
    }

    fn get_var(&self, name: String) -> QbeGenerationResult<&QbeValue> {
        self.scopes
            .iter()
            .rev()
            .filter_map(|s| s.get(&name))
            .next()
            .ok_or_else(|| QbeGenerationError::UndefinedSymbol(name))
    }

    fn declare_var_overwriting(&'a mut self, r#type: QbeType<'a>, name: String) -> QbeGenerationResult<'a, QbeValue<'a>> {
        let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
        
        let tmp = self.generate_temp(r#type.clone());

        let mut borrowed = self_cell.borrow_mut();
        let scope = (*borrowed)
            .scopes
            .last_mut()
            .expect("expected last scope to be present");

        scope.insert(name.to_owned(), tmp.to_owned());

        Ok(tmp)
    }

    fn declare_var(&'a mut self, r#type: QbeType<'a>, name: String) -> QbeGenerationResult<'a, QbeValue<'a>> {
        if self.get_var(name.clone()).is_ok() {
            return Err(QbeGenerationError::DoubleDefinition(name));
        }
        
        let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
        
        let tmp = self.generate_temp(r#type.clone());

        let mut borrowed = self_cell.borrow_mut();
        let scope = (*borrowed)
            .scopes
            .last_mut()
            .expect("expected last scope to be present");

        scope.insert(name.to_owned(), tmp.to_owned());

        Ok(tmp)
    }

    fn generate_string(&mut self, string: String) -> QbeGenerationResult<QbeValue> {
        self.unique_name_counter += 1;

        let name = format!("string.{}", self.unique_name_counter);

        let mut items: Vec<(qbe::Type, DataItem)> = Vec::new();
        let mut buf = String::new();
        for ch in string.chars() {
            if ch.is_ascii() && !ch.is_ascii_control() && ch != '"' {
                buf.push(ch)
            } else {
                if !buf.is_empty() {
                    items.push((QbeType::Integer8.into_qbe(false), DataItem::Str(buf.clone())));
                    buf.clear();
                }

                let mut buf = [0; 4];
                let len = ch.encode_utf8(&mut buf).len();

                for b in buf.iter().take(len) {
                    items.push((QbeType::Integer8.into_qbe(false), DataItem::Const(*b as u64)));
                }

                continue;
            }
        }

        if !buf.is_empty() {
            items.push((QbeType::Integer8.into_qbe(false), DataItem::Str(buf.clone())));
        }

        let len = buf.len() as u32;

        self.datadefs.push(DataDef {
            linkage: Linkage::private(),
            name: name.clone(),
            align: None,
            items,
        });
        
        let ty = QbeType::FatPointer(Indirection::new(QbeType::Integer8), len);
        
        Ok(QbeValue::Global(name, ty))
    }

    fn generate_array(
        &'a mut self,
        func: &mut Function<'a>,
        len: u32,
        items: Box<[AstNode]>,
    ) -> QbeGenerationResult<QbeValue> {
        let mut first_type: Option<QbeType> = None;
        let mut result: Vec<QbeValue> = Vec::new();

        self.unique_name_counter += 1;

        let name = format!("array.{}", self.unique_name_counter);

        for item in items {
            let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
            let item = self2.generate_expr(item, func)?;
            let ty = item.get_type();

            if let Some(ref first_type) = first_type {
                if &ty != first_type {
                    return Err(QbeGenerationError::MismatchedType("".to_string(), first_type.clone(), ty))
                }
            } else {
                first_type = Some(ty)
            }

            result.push(item)
        }

        let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });

        //let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
        let mut addr = self.generate_temp(Integer64);

        func.assign_instr(
            addr.clone().into_qbe(),
            Integer64.into_qbe(false),
            Instr::Alloc8(
                if let Some(ref ty) = first_type {
                    ty.size() * (len as u64)
                } else {
                    0
                },
            ),
        );

        for (i, value) in result.iter().enumerate() {
            let mut borrowed = self_cell.borrow_mut();
            let value_ptr = (*borrowed).generate_temp(Integer64);

            func.assign_instr(
                value_ptr.clone().into_qbe(),
                Integer64.into_qbe(false),
                Instr::Add(
                    addr.clone().into_qbe(),
                    QbeValue::Pointer(
                        (i as u64) * first_type.as_ref().unwrap().size(),
                    ).into_qbe(),
                ),
            );

            func.add_instr(Instr::Store(
                first_type.as_ref().unwrap().clone().into_qbe(false),
                value_ptr.into_qbe(),
                value.to_owned().into_qbe(),
            ));
        }

        let mut borrowed = self_cell.borrow_mut();
        (*borrowed).unique_name_counter += 1;

        let typedef = TypeDef {
            name: name.clone(),
            align: None,
            items: if let Some(ref ty) = first_type {
                vec![(Integer64.into_qbe(false), 1), (ty.clone().into_qbe(false), len as usize)]
            } else {
                // No elements
                vec![(Integer64.into_qbe(false), 1)]
            },
        };

        let mut borrowed = self_cell.borrow_mut();
        (*borrowed).typedefs.push(typedef.clone());

        addr.set_type(QbeType::Aggregate(typedef, Indirection::new(QbeType::FatPointer(Indirection::new(first_type.unwrap()), len)))).acknowledge();

        Ok(addr)
    }

    fn generate_array_from_value_pairs(
        &'a mut self,
        func: &mut Function<'a>,
        len: u32,
        items: Box<[QbeValue<'a>]>,
    ) -> QbeGenerationResult<QbeValue> {
        let mut first_type: Option<QbeType> = None;
        let mut result: Vec<QbeValue> = Vec::new();

        self.unique_name_counter += 1;

        let name = format!("array.{}", self.unique_name_counter);

        for item in items {
            let ty = item.get_type();

            if let Some(ref first_type) = first_type {
                if &ty != first_type {
                    return Err(QbeGenerationError::MismatchedType("".to_string(), first_type.clone(), ty))
                }
            } else {
                first_type = Some(ty)
            }

            result.push(item)
        }

        let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
        
        let mut addr = self.generate_temp(Integer64);

        func.assign_instr(
            addr.clone().into_qbe(),
            Integer64.into_qbe(false),
            Instr::Alloc8(
                if let Some(ref ty) = first_type {
                    ty.size() * (len as u64)
                } else {
                    0
                },
            ),
        );

        for (i, value) in result.iter().enumerate() {
            let mut borrowed = self_cell.borrow_mut();
            let value_ptr = (*borrowed).generate_temp(Integer64);

            func.assign_instr(
                value_ptr.clone().into_qbe(),
                Integer64.into_qbe(false),
                Instr::Add(
                    addr.clone().into_qbe(),
                    QbeValue::Pointer(
                        (i as u64) * first_type.as_ref().unwrap().size(),
                    ).into_qbe(),
                ),
            );

            func.add_instr(Instr::Store(
                first_type.as_ref().unwrap().clone().into_qbe(false),
                value_ptr.into_qbe(),
                value.to_owned().into_qbe(),
            ));
        }

        let mut borrowed = self_cell.borrow_mut();
        (*borrowed).unique_name_counter += 1;

        let typedef = TypeDef {
            name: name.clone(),
            align: None,
            items: if let Some(ref ty) = first_type {
                vec![(Integer64.into_qbe(false), 1), (ty.clone().into_qbe(false), len as usize)]
            } else {
                // No elements
                vec![(Integer64.into_qbe(false), 1)]
            },
        };

        let mut borrowed = self_cell.borrow_mut();
        (*borrowed).typedefs.push(typedef.clone());

        addr.set_type(QbeType::Aggregate(typedef, Indirection::new(QbeType::FatPointer(Indirection::new(first_type.unwrap()), len)))).acknowledge();

        Ok(addr)
    }

    fn generate_bin_op(
        &'a mut self,
        left: AstNode,
        op: String,
        right: AstNode,
        func: &mut Function<'a>,
    ) -> QbeGenerationResult<QbeValue> {
        let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
        let left = self2.generate_expr(left, func)?;
        let left_t = left.get_type();

        let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
        let right = self2.generate_expr(right, func)?;
        let right_t = right.get_type();

        match op.as_str() {
            "==" => {
                // Dealing with C strings
                if CSTRING_TYPES.contains(&&*left_t.to_string()) {
                    let cmp_fn = format!("{left_t}{right_t}eqcmp");

                    let tmp = self.generate_temp(QbeType::Boolean);
                    
                    let args: [(qbe::Type, qbe::Value); 2] = [
                        (left_t.into_qbe_abi(), left.into_qbe()),
                        (right_t.into_qbe_abi(), right.into_qbe()),
                    ];

                    func.assign_instr(
                        tmp.clone().into_qbe(),
                        QbeType::Boolean.into_qbe_abi(),
                        Instr::Call(cmp_fn, Vec::from(args)),
                    );

                    return Ok(tmp);
                } else if left_t.to_cmp_string() == "Fc".to_string() {
                    let cmp_fn = format!("{D}{D}eqcmp", D = left_t.to_cmp_string());

                    let QbeType::FatPointer(_, l) = left_t else {
                        unreachable!()
                    };

                    let QbeType::FatPointer(_, r) = right_t else {
                        unreachable!()
                    };

                    let tmp = self.generate_temp(QbeType::Boolean);
                    let args: [(qbe::Type, qbe::Value); 4] = [
                        (QbeType::Integer32.into_qbe_abi(), QbeValue::Integer(l as u64, QbeType::Integer32).into_qbe()),
                        (left_t.into_qbe_abi(), left.into_qbe()),
                        (QbeType::Integer32.into_qbe_abi(), QbeValue::Integer(r as u64, QbeType::Integer32).into_qbe()),
                        (right_t.into_qbe_abi(), right.into_qbe()),
                    ];

                    func.assign_instr(
                        tmp.clone().into_qbe(),
                        QbeType::Boolean.into_qbe_abi(),
                        Instr::Call(cmp_fn, Vec::from(args)),
                    );

                    return Ok(tmp);
                }

                let tmp = self.generate_temp(QbeType::Boolean);

                func.assign_instr(
                    tmp.clone().into_qbe(),
                    QbeType::Boolean.into_qbe_abi(),
                    Instr::Cmp(left_t.into_qbe_abi(), Cmp::Eq, left.into_qbe(), right.into_qbe()),
                );

                Ok(tmp)
            }
            "!=" => {
                if left_t != right_t {
                    return Ok(QbeValue::byte(1));
                }

                let tmp = self.generate_temp(QbeType::Boolean);

                func.assign_instr(
                    tmp.clone().into_qbe(),
                    QbeType::Boolean.into_qbe_abi(),
                    Instr::Cmp(left_t.into_qbe_abi(), Cmp::Ne, left.into_qbe(), right.into_qbe()),
                );

                Ok(tmp)
            }
            op => Err(QbeGenerationError::UndefinedSymbol(format!("operators::{op}"))),
        }
    }

    fn generate_func(
        &'a mut self,
        name: String,
        ret_type: QbeType<'a>,
        args: Box<[ArgMeta<'a>]>,
        code: ParseBlock,
        type_generics: &HashMap<String, Option<TypeBound>>,
        calls: Vec<Box<[QbeValue<'a>]>>
    ) -> QbeGenerationResult<Vec<Function<'a>>> {
        let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });

        let mut borrowed = self_cell.borrow_mut();
        (*borrowed).scopes.push(HashMap::new());
        
        let mut created_fns: Vec<Function<'a>> = vec![];

        // do NOT use type generics or mangling
        if name == "main" {
            let mut arguments: Vec<(qbe::Type, qbe::Value)> = Vec::new();

            for (name, r#type, _) in args.clone().iter_mut() {
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let mut tmp = self2.declare_var_overwriting(r#type.clone(), name.clone())?;

                if let QbeType::Generic(name, _) = r#type {
                    return Err(QbeGenerationError::GenericsDisallowed(name.clone()))
                };

                tmp.set_type(r#type.clone()).acknowledge();

                arguments.push((r#type.clone().into_qbe_abi(), tmp.into_qbe()));
            }

            let mut func = Function {
                linkage: Linkage::public(),
                name: name.clone(),
                arguments,
                return_ty: Some(ret_type.clone().into_qbe_abi()),
                blocks: Vec::new(),
            };

            func.add_block("start");

            let ParseBlock::Plain(ref code) = code;

            for expr in code {
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                self2.generate_expr(expr.clone(), &mut func)?;
            }

            let mut borrowed = self_cell.borrow_mut();
            (*borrowed).functions.insert(name, (ret_type.clone(), vec![("main".into(), args.clone())]));
            (*borrowed).module.add_function(func.clone());

            return Ok(vec![func])
        }
        
        let mut tg: HashMap<String, Vec<QbeType>> = HashMap::default();
        
        for call in calls.iter() {
            for (j, arg) in call.into_iter().enumerate() {
                let arg_ty = args.get(j).unwrap().1.clone();
                
                let ty = arg.get_type();

                if let QbeType::Generic(ref name, ref bound) = arg_ty {
                    if let Some(ref bound) = bound {
                        let cond = ty.matches_bound(bound.clone(), unsafe { (self as *mut Self).as_mut().unwrap() }, type_generics)?;
                       
                        if !cond {
                            return Err(QbeGenerationError::UnmetBound(name.clone(), bound.clone(), j))
                        }
                    }
                    
                    if let Some(types) = tg.get(name) {
                        if !types.contains(&arg.get_type()) {
                            tg.get_mut(name).unwrap().push(arg.get_type());
                        }
                    } else {
                        tg.insert(name.clone(), vec![arg.get_type()]);
                    }
                }
            }
        }

        for (i, call) in calls.iter().enumerate() {
            let mut arguments: Vec<(qbe::Type, qbe::Value)> = Vec::new();

            for (i, (name, r#type, _)) in args.clone().iter_mut().enumerate() {
                let mut tmp = unsafe { (self as *mut Self).as_mut().unwrap() }.declare_var_overwriting(r#type.clone(), name.clone())?;

                if let QbeType::Generic(name, _) = r#type {
                    *r#type = match tg.get(name) {
                        Some(_) => call[i].get_type(),
                        None => return Err(QbeGenerationError::UndefinedSymbol(name.clone())),
                    };
                }

                tmp.set_type(r#type.clone()).acknowledge();

                arguments.push((r#type.clone().into_qbe_abi(), tmp.into_qbe()));
            }

            let call_types = call.clone().iter().map(|c| c.get_type()).collect::<Vec<_>>();
            let name = (name.clone(), ret_type.clone(), call_types);

            let mut func = Function {
                linkage: Linkage::public(),
                name: name.mangle(),
                arguments,
                return_ty: Some(ret_type.clone().into_qbe_abi()),
                blocks: Vec::new(),
            };

            func.add_block("start");

            let ParseBlock::Plain(ref code) = code;

            for expr in code {
                unsafe { (self as *mut Self).as_mut().unwrap() }.generate_expr(expr.clone(), &mut func)?;
            }

            let args = args.iter().map(|(name, ty, d)| {
                (name.clone(), if let QbeType::Generic(name, _) = ty {
                    tg.get(name).unwrap()[i].clone()
                } else {
                    ty.clone()
                }, d.clone())
            }).collect::<Vec<_>>();

            if let Some(func) = (*self_cell.borrow_mut()).functions.get_mut(&name.0) {
                func.1.push((name.mangle(), args.clone().into_boxed_slice()))
            } else {
                (*self_cell.borrow_mut()).functions.insert(name.0.clone(), (ret_type.clone(), vec![(name.mangle(), args.clone().into_boxed_slice())]));
            };

            (*self_cell.borrow_mut()).module.add_function(func.clone());
            created_fns.push(func);
        }

        Ok(created_fns)
    }

    fn generate_independent_expr(&mut self, expr: AstNode) -> QbeGenerationResult<QbeValue> {
        match expr {
            AstNode::NumberLiteral(n) => {
                if n.fract() == 0f64 {
                    Ok(QbeValue::long(n as i64))
                } else {
                    Ok(QbeValue::double(n))
                }
            }
            AstNode::StringLiteral(s) => self.generate_string(s),
            AstNode::BooleanLiteral(b) => Ok(QbeValue::Boolean(b)),
            AstNode::NullLiteral => Ok(QbeValue::NullVoid),
            AstNode::Identifier(name) => {
                let v = self.get_var(name)?;

                Ok(v.clone())
            }
            _ => unimplemented!(),
        }
    }

    fn generate_stmt(&'a mut self, stmt: AstNode, func: &mut Function<'a>) -> QbeGenerationResult<()> {
        match stmt {
            AstNode::ReturnStmt(v) => {
                let instr = Instr::Ret(Some(self.generate_expr(v.deref().clone(), func)?.into_qbe()));

                func.add_instr(instr)
            }
            AstNode::IfStmt { cond, block } => {
                let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });

                let mut borrowed = self_cell.borrow_mut();
                (*borrowed).unique_name_counter += 1;

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let cond = self2.generate_expr(cond.deref().clone(), func)?;

                let borrowed = self_cell.borrow();
                
                let if_label = format!("cond.if.{C}", C = borrowed.unique_name_counter);
                let end_label = format!("cond.end.{C}", C = borrowed.unique_name_counter);

                func.add_instr(Instr::Jnz(cond.into_qbe(), if_label.clone(), end_label.clone()));

                func.add_block(if_label);

                let ParseBlock::Plain(block) = block;

                for stmt in block {
                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    self2.generate_expr(stmt, func)?;
                }

                func.add_block(end_label);
            }
            AstNode::DefStmt {
                name,
                value,
                def_type,
            } => {
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                let value = self2.generate_expr(value.deref().clone(), func)?;
                let vty = value.get_type();

                if let ParseType::IdentType(s) = def_type.clone() && s == "auto" {
                    let tmp = self.declare_var(vty.clone(), name.clone())?;

                    func.assign_instr(tmp.into_qbe(), vty.clone().into_qbe_abi(), Instr::Copy(value.into_qbe()));

                    return Ok(())
                }

                let ty = TypeGenerator::generate_type(def_type, unsafe { (self as *mut Self).as_mut().unwrap() }, &HashMap::new())?;
                let tmp = self.declare_var(ty.clone(), name.clone())?;
                
                if let QbeType::Aggregate(_, i) = vty {
                    if i.deref().clone() != ty {
                        return Err(QbeGenerationError::MismatchedType(name, ty, i.deref().clone()))
                    }
                } else if vty != ty {
                    return Err(QbeGenerationError::MismatchedType(name, ty, vty))
                }

                func.assign_instr(tmp.into_qbe(), ty.clone().into_qbe_abi(), Instr::Copy(value.into_qbe()));
            }
            _ => unimplemented!("Compile statement {stmt}"),
        }

        Ok(())
    }

    fn get_calls_of_func(&'a mut self, name: String, remaining_nodes: Vec<AstNode>) -> QbeGenerationResult<'a, Vec<Box<[QbeValue<'a>]>>> {
        let mut calls: Vec<Box<[QbeValue]>> = vec![];

        for node in remaining_nodes {
            if let AstNode::FnExpr { code, .. } = node {
                let ParseBlock::Plain(code) = code;

                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                calls = [calls.as_slice(), self2.get_calls_of_func(name.clone(), code.into())?.as_slice()].concat();

                continue
            }

            let AstNode::CallExpr { callee, args } = node else {
                continue
            };

            let mut new_args = vec![];

            for arg in args {
                let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                new_args.push(self2.generate_independent_expr(arg.clone())?);
            }

            let AstNode::Identifier(call_name) = callee.deref() else {
                // TODO: handle this case properly
                continue;
            };

            if &name != call_name {
                continue;
            }

            calls.push(new_args.into_boxed_slice());
        }

        Ok(calls)
    }

    fn generate_global_stmt(&'a mut self) -> QbeGenerationResult<()> {
        let vec = self.parser.to_vec();
        let mut iter = vec.into_iter();

        while let Some(stmt) = iter.next() {
            let stmt = match stmt {
                Ok(s) => s,
                Err(e) => return Err(QbeGenerationError::ParseError(e.clone())),
            };
            
            match stmt {
                AstNode::DefStmt { .. } => todo!(),
                AstNode::IncludeStmt(p) => {
                    let AstNode::Path(p) = p.as_ref() else {
                        unreachable!()
                    };

                    let search_path = p.as_ref().split_last().unwrap().1.join("/");

                    let mut msc_path =
                        PathBuf::from(format!("{search_path}/{}.msc", p.last().unwrap()));
                    let mut obj_path: Option<_> =
                        Some(PathBuf::from(format!("{S}/{}.o", p.last().unwrap(), S = search_path.clone())));

                    // Attempt lookup in installed modules directory (~/.msc/mods/)
                    if fs::File::open(msc_path.clone()).is_err() {
                        let home = std::env::var("HOME").unwrap();

                        msc_path = PathBuf::from(format!(
                            "{home}/.msc/mods/{search_path}/{}.msc",
                            p.last().unwrap()
                        ));
                        obj_path = Some(PathBuf::from(format!(
                            "{home}/.msc/mods/{search_path}/{}.o",
                            p.last().unwrap()
                        )));
                    }
                    
                    if let Some(ref p) = obj_path && !p.exists() {
                        obj_path = None;
                    }

                    // SHADOW CODEGEN

                    let reader =
                        CharReader::new(File::new(msc_path.to_str().unwrap().to_string()).unwrap());

                    let lexer = StreamedLexer::new(reader);
                    let parser = StreamedParser::new(lexer);

                    // Compile module and add it to the included modules

                    let mut shadow_cg = QbeGenerator::new(parser, obj_path);

                    shadow_cg.unique_name_counter = self.unique_name_counter + 1;
;
                    let scg2 = unsafe { (&mut shadow_cg as *mut QbeGenerator).as_mut().unwrap() };
                    let gen = scg2.generate()?.clone();

                    self.included_modules.push(gen);

                    self.unique_name_counter = shadow_cg.unique_name_counter + 1;

                    fs::File::open(msc_path.clone()).map_err(|_| {
                        QbeGenerationError::UndefinedLibrary(
                            format!("{}::{}", search_path.replace("/", "::"), p.last().unwrap())
                                .parse()
                                .unwrap(),
                        )
                    })?;
                }
                AstNode::ExternFn {
                    name,
                    ret_type,
                    args,
                } => {
                    let args: Vec<ArgMeta> = args
                        .into_iter()
                        .map(|(name, r#type, _default)| {
                            (
                                name.clone(),
                                TypeGenerator::generate_type(r#type.clone(), unsafe { (self as *mut Self).as_mut().unwrap() }, &HashMap::new())
                                    .unwrap()
                                    .clone(),
                                None,
                            )
                        })
                        .collect();

                    let r#type = TypeGenerator::generate_type(ret_type.clone(), unsafe { (self as *mut Self).as_mut().unwrap() }, &HashMap::new())?;

                    if let Some(func) = self.functions.get_mut(&name) {
                        func.1.push((name.clone(), args.clone().into_boxed_slice()))
                    } else {
                        self.functions.insert(name.clone(), (r#type, vec![(name.clone(), args.clone().into_boxed_slice())]));
                    };
                }
                AstNode::Program(_) => unreachable!(),
                AstNode::FnExpr {
                    name,
                    ret_type,
                    args,
                    code,
                    type_generics
                } => {
                    let self_cell = RefCell::new(unsafe { (self as *mut Self).as_mut().unwrap() });
                    
                    let args: Vec<ArgMeta> = IntoIterator::into_iter(args)
                        .map(|(name, r#type, _default)| {
                            (
                                name.clone(),
                                TypeGenerator::generate_type(r#type.clone(), unsafe { (self as *mut Self).as_mut().unwrap() }, &type_generics)
                                    .unwrap()
                                    .clone(),
                                None,
                            )
                        })
                        .collect();

                    // TODO: Allow returning generics
                    let r#type = TypeGenerator::generate_type(ret_type.clone(), unsafe { (self as *mut Self).as_mut().unwrap() }, &HashMap::new())?;
                    
                    let remaining_nodes = iter.clone().filter_map(|r| r.clone().ok()).collect::<Vec<_>>();

                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    let calls = self2.get_calls_of_func(name.clone(), remaining_nodes)?;

                    let self2 = unsafe { (self as *mut Self).as_mut().unwrap() };
                    self2.generate_func(
                        name.clone(),
                        r#type.clone(),
                        args.into_boxed_slice(),
                        code.clone(),
                        &type_generics,
                        calls,
                    )?;
                }
                stmt => unimplemented!("Compile statement {stmt}"),
            }
        }

        Ok(())
    }

    pub fn new(parser: StreamedParser, obj_file_path: Option<PathBuf>) -> Self {
        Self {
            file_path: parser.lexer.reader.reader.path().to_path_buf(),
            unique_name_counter: 0,
            module: Default::default(),
            types: HashMap::from([
                ("i8".into(), QbeType::Integer8),
                ("i16".into(), QbeType::Integer16),
                ("i32".into(), QbeType::Integer32),
                ("i64".into(), Integer64),
                (
                    "u8".into(),
                    QbeType::Unsigned(Indirection::new(QbeType::Integer8)),
                ),
                (
                    "u16".into(),
                    QbeType::Unsigned(Indirection::new(QbeType::Integer16)),
                ),
                ("bool".into(), QbeType::Boolean),
                ("f32".into(), QbeType::Float32),
                ("f64".into(), QbeType::Float64),
                ("null".into(), QbeType::NullVoid),
            ]),
            scopes: vec![],
            functions: HashMap::new(),
            datadefs: vec![],
            parser,
            included_modules: vec![],
            typedefs: vec![],
            associated_obj_path: obj_file_path,
        }
    }
}