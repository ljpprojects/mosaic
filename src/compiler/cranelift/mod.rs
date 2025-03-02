#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![forbid(unsafe_code)]

use crate::compiler::traits::CompilationModule;
pub mod builders;
pub mod linker;
pub mod mangle;
pub mod meta;
pub mod module;
pub mod trace;
pub mod types;
pub mod value;

use crate::cli::Command;
use crate::compiler::analyser::{get_usages_of, PreoptEngine, UsageKind};
use crate::compiler::cranelift::builders::VariableBuilder;
use crate::compiler::cranelift::mangle::{mangle_function, mangle_method};
use crate::compiler::cranelift::meta::{FunctionMeta, MustFreeMeta};
use crate::compiler::cranelift::module::CraneliftModule;
use crate::compiler::cranelift::trace::{ContextKind, Trace};
use crate::compiler::cranelift::types::{CraneliftType as Type, CraneliftType, CraneliftTypeGenerator};
use crate::compiler::traits::{CompilationType, TypeGenerator};
use crate::errors::CompilationError;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, MatchArm, Modifier, ParseBlock, ParseType, StreamedParser};
use crate::reader::CharReader;
use crate::utils::Indirection;
use colored::Colorize;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::immediates::Imm64;
use cranelift_codegen::ir::stackslot::StackSize;
use cranelift_codegen::ir::{AbiParam, Block, FuncRef, Function, GlobalValue, InstBuilder, MemFlags, Signature, StackSlot, StackSlotData, StackSlotKind, UserFuncName, Value};
use cranelift_codegen::isa::{Builder, CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::Configurable;
use cranelift_codegen::{ir, isa, settings, Context};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{default_libcall_names, DataDescription, FuncId, Linkage, Module};
use cranelift_native;
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::any::Any;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use cranelift_codegen::ir::entities::AnyEntity::SigRef;

macro_rules! get_fn {
    ($self: expr, $name:expr) => {
        match $self.functions.get($name) {
            Some(f) => Some(f),
            None => {
                let mut res = None;

                for lib in $self.included_modules.iter() {
                    match lib.lookup_func($name) {
                        Some(f) => {
                            res = Some(f);
                            break;
                        }
                        None => continue,
                    }
                }

                res
            }
        }
    };
}

macro_rules! get_fn_variant {
    ($self: expr, $name:expr) => {
        match $self.function_variants.get($name) {
            Some(v) => Some(v.clone()),
            None => {
                let mut res = None;
                for lib in $self.included_modules.iter() {
                    match lib.lookup_func_variants($name) {
                        Some(v) => {
                            res = Some(v);
                            break;
                        }
                        None => continue,
                    }
                }
                
                res.map(|v| v.iter().map(|(a, b)| (a.downcast_ref::<CraneliftType>().unwrap().clone(), b.iter().map(|a| a.downcast_ref::<CraneliftType>().unwrap().clone()).collect::<Vec<_>>())).collect::<Vec<_>>())
            }
        }
    };
}

pub struct CraneliftGenerator {
    /// A counter for unique names.
    counter: usize,

    /// The name of the module that is being compiled.
    module_name: String,

    /// The number of functions that have been compiled so far in this module.
    fn_counter: u32,

    /// The path to the Mosaic file being compiled.
    file_path: PathBuf,

    /// The parser.
    parser: StreamedParser,

    /// Every variant of the compiled functions.
    function_variants: HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>>,

    /// A map of mangled function names to their metadata.
    functions: HashMap<String, FunctionMeta>,

    /// Used to create variables.
    var_builder: VariableBuilder,

    /// The cranelift ObjectModule for generated objects for the output target.
    module: ObjectModule,

    /// The calling convention to use.
    call_conv: CallConv,

    /// The cranelift OwnedTargetIsa primarily used for getting the pointer width/type.
    isa: OwnedTargetIsa,

    /// Used to get the target triple when compiling other modules (marked for removal)
    isa_builder: Builder,

    /// Used to compile types.
    tg: CraneliftTypeGenerator,

    /// A list of every module that the current module has included.
    included_modules: Vec<CraneliftModule>,

    /// A function-scoped list of values that will be freed at the end of their function, not scopes.
    auto_frees: Vec<HashSet<Value>>,

    /// A function-scoped list of tasks that will be executed in LIFO order at the end of a function, not scope.
    deferred_items: Vec<Vec<ParseBlock>>,

    /// A list of all functions that were marked with the 'alloc' modifier.
    allocator_fns: HashSet<String>,

    /// A list of all functions that were marked with the 'dealloc' modifier.
    deallocator_fns: HashSet<String>,

    /// A list of all values that must be freed.
    must_frees: HashSet<MustFreeMeta>,

    /// Stores the argument given to the program
    command: Option<Command>,
    
    /// A map of mangled function names to their cranelift FuncId for calling function pointers.
    fn_refs: HashMap<String, (Function, FuncId)>,
}

impl CraneliftGenerator {
    pub fn new(parser: StreamedParser, isa_builder: Builder, command: Option<Command>) -> Self {
        let file_path: PathBuf = if let Some(Command::Build { file, .. }) = command.clone() {
            file.into()
        } else {
            parser.lexer.reader.reader.path().into()
        };

        let mut shared_builder = settings::builder();

        shared_builder.enable("is_pic").unwrap();
        shared_builder.set("enable_pcc", "false").unwrap();
        shared_builder.enable("enable_jump_tables").unwrap();
        shared_builder.enable("enable_verifier").unwrap();
        shared_builder.enable("enable_alias_analysis").unwrap();

        shared_builder.set("unwind_info", "false").unwrap();
        shared_builder.set("opt_level", "speed_and_size").unwrap();
        shared_builder
            .set("regalloc_algorithm", "backtracking")
            .unwrap();

        let shared_flags = settings::Flags::new(shared_builder);

        let isa = isa_builder.finish(shared_flags).unwrap();

        let call_conv = isa.default_call_conv();

        let module_name = file_path.file_stem().unwrap().to_str().unwrap().to_string();

        let obj_builder =
            ObjectBuilder::new(isa.clone(), module_name.clone(), default_libcall_names()).unwrap();

        let module = ObjectModule::new(obj_builder);

        Self {
            counter: 0,
            module_name,
            file_path,
            parser,
            function_variants: Default::default(),
            functions: Default::default(),
            var_builder: VariableBuilder::new(&isa),
            module,
            call_conv,
            isa,
            fn_counter: 0,
            isa_builder,
            tg: CraneliftTypeGenerator::new(),
            included_modules: vec![],
            auto_frees: vec![],
            deferred_items: vec![],
            allocator_fns: HashSet::new(),
            deallocator_fns: HashSet::new(),
            must_frees: HashSet::new(),
            command,
            fn_refs: HashMap::new(),
        }
    }

    pub fn compile_bit_op(
        &mut self,
        op: &String,
        left: &AstNode,
        right: &AstNode,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        match &**op {
            "=" => {
                let AstNode::Identifier(name) = left else {
                    if let AstNode::IdxAccess(of, idx) = left {
                        let (right, rty) = self.compile_body_expr(right, func, trace)?;

                        let (of, ty) = self.compile_body_expr(
                            of,
                            func,
                            &trace.nested_ctx(ContextKind::RightOp(op.clone())),
                        )?;

                        let (idx, _) = self.compile_body_expr(
                            idx,
                            func,
                            &mut trace.nested_ctx(ContextKind::Idx),
                        )?;

                        let inner_ty = ty.inner().unwrap();
                        let inner_ty_size = inner_ty.size_bytes(&self.isa) as i64;

                        let offset = func.ins().imul_imm(idx, inner_ty_size);
                        let computed_addr = func.ins().iadd(of, offset);

                        // TODO: Type checking

                        func.ins().store(
                            MemFlags::trusted().with_checked(),
                            right,
                            computed_addr,
                            0,
                        );

                        return Ok((right, rty));
                    } else if let AstNode::PrefixOp(op, val) = left {
                        if &**op == "*" {
                            let (addr, ty) = self.compile_body_expr(val, func, trace)?;
                            let (right, rty) = self.compile_body_expr(right, func, trace)?;

                            // TODO: Type checking

                            func.ins()
                                .store(MemFlags::trusted().with_checked(), right, addr, 0);

                            return Ok((right, rty));
                        } else {
                            todo!("Assignment op with lhs {left}")
                        }
                    } else {
                        todo!("Assignment op with lhs {left}")
                    }
                };

                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                self.var_builder.set_var(
                    func,
                    name,
                    &right,
                    &rty,
                    self.file_path.clone(),
                    trace,
                )?;

                Ok((right, rty))
            }
            ">>" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (amt, aty) = self.compile_body_expr(right, func, trace)?;

                assert!(lty.is_numeric() && aty.is_numeric());

                if lty.is_signed() {
                    Ok((func.ins().sshr(left, amt), lty))
                } else {
                    Ok((func.ins().ushr(left, amt), lty))
                }
            }
            "<<" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (amt, aty) = self.compile_body_expr(right, func, trace)?;

                assert!(lty.is_numeric() && aty.is_numeric());

                Ok((func.ins().ishl(left, amt), lty))
            }
            "&" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (amt, aty) = self.compile_body_expr(right, func, trace)?;

                assert!(lty.is_numeric() && aty.is_numeric());

                Ok((func.ins().band(left, amt), lty))
            }
            "|" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (amt, aty) = self.compile_body_expr(right, func, trace)?;

                assert!(lty.is_numeric() && aty.is_numeric());

                Ok((func.ins().bor(left, amt), lty))
            }
            _ => self.compile_num_op(op, left, right, func, trace),
        }
    }

    pub fn compile_cmp_op(
        &mut self,
        op: &String,
        left: &AstNode,
        right: &AstNode,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        match &**op {
            "==" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                if !lty.cmp_eq(Rc::new(rty)) {
                    return Ok((func.ins().iconst(ir::types::I8, 0), Type::Bool));
                }

                let ty_size = func
                    .ins()
                    .iconst(ir::types::I64, lty.size_bytes(&self.isa) as i64);

                if lty.is_pointer() {
                    Ok((
                        func.call_memcmp(self.isa.frontend_config(), left, right, ty_size),
                        Type::Bool,
                    ))
                } else if lty.is_numeric() {
                    Ok((
                        if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                            func.ins().fcmp(FloatCC::Equal, left, right)
                        } else {
                            func.ins().icmp(IntCC::Equal, left, right)
                        },
                        Type::Bool,
                    ))
                } else if matches!(lty, Type::Bool) {
                    Ok((func.ins().icmp(IntCC::Equal, left, right), Type::Bool))
                } else {
                    todo!()
                }
            }
            "!=" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                if !lty.cmp_eq(Rc::new(rty)) {
                    return Ok((func.ins().iconst(ir::types::I8, 0), Type::Bool));
                }

                let ty_size = func
                    .ins()
                    .iconst(ir::types::I64, lty.size_bytes(&self.isa) as i64);

                if lty.is_pointer() {
                    let eq = func.call_memcmp(self.isa.frontend_config(), left, right, ty_size);

                    Ok((func.ins().bnot(eq), Type::Bool))
                } else if lty.is_numeric() || matches!(lty, Type::Bool) {
                    Ok((
                        if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                            func.ins().fcmp(FloatCC::NotEqual, left, right)
                        } else {
                            func.ins().icmp(IntCC::NotEqual, left, right)
                        },
                        Type::Bool,
                    ))
                } else if matches!(lty, Type::Bool) {
                    Ok((func.ins().icmp(IntCC::NotEqual, left, right), Type::Bool))
                } else {
                    todo!()
                }
            }
            "&&" => {
                let (left, _) = self.compile_body_expr(left, func, trace)?;
                let (right, _) = self.compile_body_expr(right, func, trace)?;

                Ok((func.ins().band(left, right), Type::Bool))
            }
            ">" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let res = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    func.ins().fcmp(FloatCC::GreaterThan, left, right)
                } else {
                    func.ins().icmp(IntCC::SignedGreaterThan, left, right)
                };

                Ok((res, Type::Bool))
            }
            "<" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let res = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    func.ins().fcmp(FloatCC::LessThan, left, right)
                } else {
                    func.ins().icmp(IntCC::SignedLessThan, left, right)
                };

                Ok((res, Type::Bool))
            }
            op => Err(Box::new([CompilationError::UndefinedOperator(
                self.file_path.clone(),
                trace.clone(),
                op.to_string(),
            )])),
        }
    }

    pub fn compile_num_op(
        &mut self,
        op: &String,
        left: &AstNode,
        right: &AstNode,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        match &**op {
            "+" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fadd(left, right), Type::Float64)
                } else {
                    (func.ins().iadd(left, right), lty)
                };

                Ok((res, ty))
            }
            "-" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fsub(left, right), lty)
                } else {
                    (func.ins().isub(left, right), lty)
                };

                Ok((res, ty))
            }
            "*" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fmul(left, right), Type::Float64)
                } else {
                    (func.ins().imul(left, right), lty)
                };

                Ok((res, ty))
            }
            "/" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fdiv(left, right), Type::Float64)
                } else if lty.is_signed() {
                    (func.ins().sdiv(left, right), lty)
                } else {
                    (func.ins().udiv(left, right), lty)
                };

                Ok((res, ty))
            }

            "%" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if lty.is_signed() {
                    (func.ins().srem(left, right), Type::Int64)
                } else {
                    (func.ins().urem(left, right), lty.to_unsigned().unwrap().downcast_ref::<CraneliftType>().unwrap().clone())
                };

                Ok((res, ty))
            }
            _ => self.compile_cmp_op(op, left, right, func, trace),
        }
    }

    pub fn compile_prefix_op(
        &mut self,
        op: &String,
        right: &AstNode,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        match &**op {
            "-" => {
                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                assert!(rty.is_signed() && rty.is_numeric());

                if matches!(rty, Type::Float64 | Type::Float32) {
                    Ok((func.ins().fneg(right), rty))
                } else {
                    Ok((func.ins().ineg(right), rty))
                }
            }
            "!" => {
                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                assert!(matches!(rty, Type::Bool));

                Ok((func.ins().ineg(right), Type::Bool))
            }
            "&" => {
                if let AstNode::Identifier(name) = right {
                    if let Some(f) = get_fn!(self, name) {
                        let user_name = UserExternalName {
                            namespace: 0,
                            index: self.functions.get(name).unwrap().index
                        };

                        let name_ref: UserExternalNameRef = func.func.declare_imported_user_function(user_name);

                        let sig_ref = func.import_signature(self.functions.get(name).unwrap().sig.clone());

                        let data = ExtFuncData {
                            name: ExternalName::User(name_ref),
                            signature: sig_ref,
                            colocated: true,
                        };

                        let fn_ref = func.import_function(data);
                        
                        let ptr = func.ins().func_addr(self.isa.pointer_type(), fn_ref);
                        let ty = Type::FuncPtr {
                            ret_type: Box::new(f.return_type.downcast_ref::<CraneliftType>().unwrap().clone()),
                            arg_types: f.arg_meta.iter().map(|(_, b)| Box::new(b.downcast_ref::<CraneliftType>().unwrap().clone())).collect(),
                        };
                        
                        return Ok((ptr, ty))
                    }
                    
                    let (ptr, ty) =
                        self.var_builder
                            .get_var_ptr(func, name, self.file_path.clone(), trace)?;

                    Ok((ptr, Type::CPtr(Indirection::new(ty))))
                } else {
                    Err(Box::new([CompilationError::UndefinedOperator(self.file_path.clone(), trace.clone(), "& (on an expression)".to_string())]))
                }
            }
            "*" => {
                let (ptr, pty) = self.compile_body_expr(right, func, trace)?;

                let value = func.ins().load(
                    pty.inner().unwrap().downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa),
                    self.var_builder.flags,
                    ptr,
                    0,
                );

                Ok((value, pty.inner().unwrap().downcast_ref::<CraneliftType>().unwrap().clone()))
            }
            _ => todo!("Handle error here"),
        }
    }

    pub fn compile_body_expr(
        &mut self,
        expr: &AstNode,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        match expr {
            AstNode::SizeOf(ty) => Ok((
                func.ins().iconst(Type::Int32.into_cranelift(&self.isa), self.tg.compile_type_no_tgs(ty, &self.isa).size_bytes(&self.isa) as i64),
                Type::Int32
            )),
            AstNode::NumberLiteral(i) if i.fract() == 0f64 => {
                let ty = Type::Int32;

                Ok((func.ins().iconst(ir::types::I32, Imm64::new(*i as i64)), ty))
            }
            AstNode::NumberLiteral(i) => Ok((func.ins().f64const(*i), Type::Float64)),
            AstNode::ByteLiteral(b) => Ok((
                func.ins().iconst(ir::types::I8, Imm64::new(*b as i64)),
                Type::Int8,
            )),
            AstNode::StringLiteral(s) => self.compile_string(s, func),
            AstNode::ArrayLiteral(a) => self.compile_array(a, func),
            AstNode::BooleanLiteral(b) if *b => {
                Ok((func.ins().iconst(ir::types::I8, Imm64::new(1)), Type::Bool))
            }
            AstNode::BooleanLiteral(_) => {
                Ok((func.ins().iconst(ir::types::I8, Imm64::new(0)), Type::Bool))
            }
            AstNode::NullLiteral => {
                Ok((func.ins().iconst(ir::types::I8, Imm64::new(0)), Type::Null))
            }
            AstNode::Identifier(i) => {
                Ok(self
                    .var_builder
                    .get_var(func, i, self.file_path.clone(), trace)?)
            }
            AstNode::InfixOp(l, o, r) => self.compile_bit_op(o, l, r, func, trace),
            AstNode::PrefixOp(op, r) => self.compile_prefix_op(op, r, func, trace),
            AstNode::PostfixOp(_, _) => todo!(),
            AstNode::Path(_) => todo!(),
            AstNode::MemberExpr(_) => todo!(),
            AstNode::IdxAccess(of, idx) => {
                let (of, ty) = self.compile_body_expr(of, func, trace)?;
                let (mut idx, ity) =
                    self.compile_body_expr(idx, func, &trace.nested_ctx(ContextKind::Idx))?;

                if ity.size_bytes(&self.isa) < self.isa.pointer_bytes() {
                    idx = func.ins().uextend(self.isa.pointer_type(), idx)
                }

                println!("{ty}");

                let inner_ty = ty.inner().unwrap();
                let inner_ty_size = inner_ty.size_bytes(&self.isa) as i64;

                let offset = func.ins().imul_imm(idx, inner_ty_size);
                let computed_addr = func.ins().iadd(of, offset);

                Ok((
                    func.ins().load(
                        inner_ty.downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa),
                        MemFlags::trusted().with_checked(),
                        computed_addr,
                        0,
                    ),
                    inner_ty.downcast_ref::<CraneliftType>().unwrap().clone(),
                ))
            }
            AstNode::CallExpr { callee, args } => {
                let AstNode::Identifier(name) = callee.as_ref() else {
                    let AstNode::Path(p) = callee.as_ref() else {
                        let AstNode::MemberExpr(p) = callee.as_ref() else {
                            panic!("Implement error here (invalid callee)")
                        };

                        assert_eq!(p.len(), 2); // TODO: Handle this error case properly

                        let this =
                            self.var_builder
                                .get_var(func, &p[0], self.file_path.clone(), trace)?;
                        let method_name = p.last().unwrap();

                        let mut value_args = vec![this.0];
                        let mut arg_types = vec![this.1.clone()];

                        for arg in args.iter() {
                            let expr = self.compile_body_expr(
                                arg,
                                func,
                                &trace.nested_ctx(ContextKind::FuncArg(method_name.clone())),
                            )?;

                            value_args.push(expr.0);

                            arg_types.push(expr.1);
                        }
                        
                        let Some(variant) = get_fn_variant!(self, method_name) else {
                            return Err(Box::new([CompilationError::InvalidSignature(
                                self.file_path.clone(),
                                trace.clone(),
                                method_name.clone(),
                                Rc::new(Type::Any),
                                arg_types.iter().map(|t| Rc::new(t.clone()) as Rc<dyn CompilationType>).collect(),
                            )]));
                        };

                        let vec = variant
                            .iter()
                            .filter(|(_, args)| {
                                arg_types
                                    .iter()
                                    .enumerate()
                                    .all(|(i, t)| t.cmp_eq(Rc::new(args.get(i).unwrap().clone()) as Rc<dyn CompilationType>))
                            })
                            .collect::<Vec<_>>();

                        let Some((ret_type, _)) = vec.first() else {
                            return Err(Box::new([CompilationError::InvalidSignature(
                                self.file_path.clone(),
                                trace.clone(),
                                method_name.clone(),
                                Rc::new(Type::Any) as Rc<dyn CompilationType>,
                                arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                            )]));
                        };

                        let mangled_name = mangle_method(
                            &this.1.to_string(),
                            method_name,
                            arg_types.as_slice(),
                            ret_type,
                        );

                        let Some(fn_meta) = get_fn!(self, &mangled_name) else {
                            return Err(Box::new([CompilationError::InvalidSignature(
                                self.file_path.clone(),
                                trace.clone(),
                                method_name.clone(),
                                Rc::new(ret_type.clone()) as Rc<dyn CompilationType>,
                                arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                            )]));
                        };

                        let fid = self
                            .module
                            .declare_function(&mangled_name, Linkage::Import, &fn_meta.sig)
                            .unwrap();

                        let local_func = self.module.declare_func_in_func(fid, func.func);

                        let ret = func.ins().call(local_func, value_args.as_slice());
                        let ret = func
                            .inst_results(ret)
                            .first().copied()
                            .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                        if fn_meta.modifiers.contains(&Modifier::AutoFree) {
                            if self.auto_frees.len() == 0 {
                                self.auto_frees.push(HashSet::new());
                            }

                            self.auto_frees.last_mut().unwrap().insert(ret.clone());
                        } else if fn_meta.modifiers.contains(&Modifier::MustFree) {
                            self.must_frees
                                .insert((ret.clone(), mangled_name.clone()).into());
                        }

                        if value_args.len() != 0 && fn_meta.modifiers.contains(&Modifier::Dealloc) {
                            for item in self.must_frees.clone() {
                                if item.value != ret.clone() {
                                    continue;
                                }

                                self.must_frees.remove(&item);

                                break;
                            }
                        }

                        return Ok((ret, fn_meta.return_type.clone().downcast_ref::<CraneliftType>().unwrap().clone()));
                    };

                    assert_eq!(p.len(), 2); // TODO: Handle this error case properly

                    let of = p.first().unwrap();
                    let method_name = p.last().unwrap();

                    let mut value_args = vec![];
                    let mut arg_types = vec![];

                    for arg in args.iter() {
                        let expr = self.compile_body_expr(
                            arg,
                            func,
                            &trace.nested_ctx(ContextKind::FuncArg(method_name.clone())),
                        )?;

                        value_args.push(expr.0);

                        arg_types.push(expr.1);
                    }

                    let Some(variant) = get_fn_variant!(self, method_name) else {
                        return Err(Box::new([CompilationError::InvalidSignature(
                            self.file_path.clone(),
                            trace.clone(),
                            format!("{of}::{method_name}"),
                            Rc::new(Type::Any) as Rc<dyn CompilationType>,
                            arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                        )]));
                    };

                    let vec = variant
                        .iter()
                        .filter(|(_, args)| {
                            arg_types
                                .iter()
                                .enumerate()
                                .all(|(i, t)| t.cmp_eq(Rc::new(args.get(i).unwrap().clone()) as Rc<dyn CompilationType>))
                        })
                        .collect::<Vec<_>>();

                    let Some((ret_type, _)) = vec.first() else {
                        return Err(Box::new([CompilationError::InvalidSignature(
                            self.file_path.clone(),
                            trace.clone(),
                            method_name.clone(),
                            Rc::new(Type::Any) as Rc<dyn CompilationType>,
                            arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                        )]));
                    };

                    let mangled_name =
                        mangle_method(of, method_name, arg_types.as_slice(), ret_type);

                    let Some(fn_meta) = get_fn!(self, &mangled_name) else {
                        return Err(Box::new([CompilationError::InvalidSignature(
                            self.file_path.clone(),
                            trace.clone(),
                            method_name.clone(),
                            Rc::new(ret_type.clone()) as Rc<dyn CompilationType>,
                            arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                        )]));
                    };

                    let fid = self
                        .module
                        .declare_function(&mangled_name, Linkage::Import, &fn_meta.sig)
                        .unwrap();

                    let local_func = self.module.declare_func_in_func(fid, func.func);

                    let ret = func.ins().call(local_func, value_args.as_slice());
                    let ret = func
                        .inst_results(ret)
                        .first()
                        .map(|v| v.clone())
                        .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                    if fn_meta.modifiers.contains(&Modifier::AutoFree) {
                        if self.auto_frees.len() == 0 {
                            self.auto_frees.push(HashSet::new());
                        }

                        self.auto_frees.last_mut().unwrap().insert(ret.clone());
                    } else if fn_meta.modifiers.contains(&Modifier::MustFree) {
                        self.must_frees
                            .insert((ret.clone(), mangled_name.clone()).into());
                    }

                    if value_args.len() != 0 && fn_meta.modifiers.contains(&Modifier::Dealloc) {
                        for item in self.must_frees.clone() {
                            if item.value != ret.clone() {
                                continue;
                            }

                            self.must_frees.remove(&item);

                            break;
                        }
                    }

                    return Ok((ret, fn_meta.return_type.downcast_ref::<CraneliftType>().unwrap().clone()));
                };

                let mut value_args = vec![];
                let mut arg_types = vec![];

                for arg in args.iter() {
                    let expr = self.compile_body_expr(
                        arg,
                        func,
                        &trace.nested_ctx(ContextKind::FuncArg(name.clone())),
                    )?;

                    value_args.push(expr.0);

                    arg_types.push(expr.1);
                }
                
                // we need to call a function pointer
                if let Ok((f, Type::FuncPtr { ret_type, arg_types })) = self.var_builder.get_var(func, name, self.file_path.clone(), trace) {
                    let mut signature = self.module.make_signature();
                    
                    signature.returns.push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
                    signature.params.extend(arg_types.iter().map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))));
                    
                    let sig_ref = func.import_signature(signature);
                    
                    let ret = func.ins().call_indirect(sig_ref, f, value_args.as_slice());
                    let ret = func
                        .inst_results(ret)
                        .first()
                        .copied()
                        .unwrap_or(func.ins().iconst(ir::types::I8, 0));
                    
                    return Ok((ret, ret_type.deref().clone()))
                }

                let Some(fn_meta) = get_fn!(self, name) else {
                    if let Some(variant) = get_fn_variant!(self, name) {
                        let vec = variant
                            .iter()
                            .filter(|(_, args)| {
                                arg_types
                                    .iter()
                                    .enumerate()
                                    .all(|(i, t)| t.cmp_eq(Rc::new(args.get(i).unwrap().clone()) as Rc<dyn CompilationType>))
                            })
                            .collect::<Vec<_>>();

                        let Some((ret_type, _)) = vec.first() else {
                            return Err(Box::new([CompilationError::InvalidSignature(
                                self.file_path.clone(),
                                trace.clone(),
                                name.clone(),
                                Rc::new(Type::Any) as Rc<dyn CompilationType>,
                                arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                            )]));
                        };

                        let mangled_name = mangle_function(name, arg_types.as_slice(), ret_type);

                        let Some(fn_meta) = get_fn!(self, &mangled_name) else {
                            return Err(Box::new([CompilationError::InvalidSignature(
                                self.file_path.clone(),
                                trace.clone(),
                                name.clone(),
                                Rc::new(ret_type.clone()) as Rc<dyn CompilationType>,
                                arg_types.into_iter().map(|t| Rc::new(t) as Rc<dyn CompilationType>).collect(),
                            )]));
                        };

                        let fid = self
                            .module
                            .declare_function(&mangled_name, Linkage::Import, &fn_meta.sig)
                            .unwrap();

                        let local_func = self.module.declare_func_in_func(fid, func.func);

                        let ret = func.ins().call(local_func, value_args.as_slice());
                        let ret = func
                            .inst_results(ret)
                            .first()
                            .map(|v| v.clone())
                            .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                        if fn_meta.modifiers.contains(&Modifier::AutoFree) {
                            if self.auto_frees.len() == 0 {
                                self.auto_frees.push(HashSet::new());
                            }

                            self.auto_frees.last_mut().unwrap().insert(ret.clone());
                        } else if fn_meta.modifiers.contains(&Modifier::MustFree) {
                            self.must_frees
                                .insert((ret.clone(), mangled_name.clone()).into());
                        }

                        if value_args.len() != 0 && fn_meta.modifiers.contains(&Modifier::Dealloc) {
                            for item in self.must_frees.clone() {
                                if item.value != ret.clone() {
                                    continue;
                                }

                                self.must_frees.remove(&item);

                                break;
                            }
                        }

                        return Ok((ret, fn_meta.return_type.downcast_ref::<CraneliftType>().unwrap().clone()));
                    }

                    let (f, fty) = self
                        .var_builder
                        .get_var(func, name, self.file_path.clone(), trace)
                        .map_err(|_| {
                            Box::from(
                                [CompilationError::UndefinedFunction(
                                    self.file_path.clone(),
                                    trace.clone(),
                                    name.clone(),
                                )]
                                .as_slice(),
                            )
                        })?;

                    let Type::FuncPtr {
                        ret_type,
                        arg_types,
                    } = fty
                    else {
                        return Err(Box::from(
                            [CompilationError::UndefinedFunction(
                                self.file_path.clone(),
                                trace.clone(),
                                name.clone(),
                            )]
                            .as_slice(),
                        ));
                    };

                    let mut sig = Signature::new(self.isa.default_call_conv());

                    sig.returns.push(AbiParam::new(
                        ret_type.deref().clone().into_cranelift(&self.isa),
                    ));
                    sig.params.extend(
                        arg_types
                            .iter()
                            .map(|t| AbiParam::new(t.deref().clone().into_cranelift(&self.isa))),
                    );

                    let fid = self
                        .module
                        .declare_function(name, Linkage::Import, &sig)
                        .unwrap();

                    let local_func = self.module.declare_func_in_func(fid, func.func);

                    let ret = func.ins().call(local_func, value_args.as_slice());

                    let ret = func
                        .inst_results(ret)
                        .first()
                        .map(|v| v.clone())
                        .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                    return Ok((ret, ret_type.deref().clone()));
                };

                let fid = self
                    .module
                    .declare_function(name, Linkage::Import, &fn_meta.sig)
                    .unwrap();

                let local_func = self.module.declare_func_in_func(fid, func.func);

                let ret = func.ins().call(local_func, value_args.as_slice());
                let ret = func
                    .inst_results(ret)
                    .first()
                    .map(|v| v.clone())
                    .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                if fn_meta.modifiers.contains(&Modifier::AutoFree) {
                    if self.auto_frees.len() == 0 {
                        self.auto_frees.push(HashSet::new());
                    }

                    self.auto_frees.last_mut().unwrap().insert(ret.clone());
                } else if fn_meta.modifiers.contains(&Modifier::MustFree) {
                    self.must_frees.insert((ret.clone(), name.clone()).into());
                }

                if value_args.len() != 0 && fn_meta.modifiers.contains(&Modifier::Dealloc) {
                    for item in self.must_frees.clone() {
                        if item.value != ret.clone() {
                            continue;
                        }

                        self.must_frees.remove(&item);

                        break;
                    }
                }

                Ok((ret, fn_meta.return_type.downcast_ref::<CraneliftType>().unwrap().clone()))
            }
            AstNode::AsExpr(val, ty) => {
                let (val, vty) = self.compile_body_expr(val, func, &trace)?;
                let ty = self.tg.compile_type_no_tgs(ty, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone();

                match (vty.clone(), ty.clone()) {
                    (Type::CPtr(_), Type::CPtr(_)) => Ok((val, ty)),
                    (Type::Slice(..), Type::Slice(..)) => Ok((val, ty)),
                    (Type::Slice(..), Type::CPtr(..)) => Ok((val, ty)),
                    (Type::FatPtr(..), Type::CPtr(..)) => Ok((val, ty)),
                    (Type::CPtr(_), Type::FatPtr(_)) => Ok((val, ty)),
                    (Type::Slice(inner, len), Type::FatPtr(..)) => {
                        let slot = func.create_sized_stack_slot(StackSlotData {
                            kind: StackSlotKind::ExplicitSlot,
                            size: (len * inner.size_bytes(&self.isa) as u32 + 4) as StackSize,
                            align_shift: 0,
                        });

                        let len_meta = func.ins().iconst(Type::Int32.into_cranelift(&self.isa), len as i64);

                        func.ins().stack_store(len_meta, slot, 0);

                        let ptr = func.ins().stack_addr(self.isa.pointer_type(), slot, 4);

                        let size_data = func.ins().iconst(self.isa.pointer_type(), len as i64 * inner.size_bytes(&self.isa) as i64 + 1);
                        func.call_memcpy(self.isa.frontend_config(), ptr, val, size_data);

                        let ptr = func.ins().stack_addr(self.isa.pointer_type(), slot, 0);

                        Ok((ptr, ty))
                    },
                    (from, Type::CPtr(i)) if from.is_pointer() && matches!(i.deref(), Type::Any) => Ok((val, ty)),
                    (Type::CPtr(i), to) if to.is_pointer() && matches!(i.deref(), Type::Any) => Ok((val, ty)),
                    (from, Type::Float32 | Type::Float64) if from.is_numeric() => {
                        if from.is_signed() {
                            Ok((func.ins().fcvt_from_sint(ty.clone().into_cranelift(&self.isa), val), ty))
                        } else {
                            Ok((func.ins().fcvt_from_uint(ty.clone().into_cranelift(&self.isa), val), ty))
                        }
                    }
                    (Type::Float32 | Type::Float64, to) if to.is_numeric() => {
                        if to.is_signed() {
                            Ok((func.ins().fcvt_to_sint(to.clone().into_cranelift(&self.isa), val), to))
                        } else {
                            Ok((func.ins().fcvt_to_uint(to.clone().into_cranelift(&self.isa), val), to))
                        }
                    }
                    (Type::Int64, p) if p.is_pointer() => Ok((val, ty)),
                    (p, Type::Int64) if p.is_pointer() => Ok((val, ty)),
                    (from, to)
                        if (from.is_numeric() || matches!(from, Type::Bool)) && to.is_numeric() =>
                    {
                        let casted = if from.size_bytes(&self.isa) > to.size_bytes(&self.isa) {
                            func.ins()
                                .ireduce(to.clone().into_cranelift(&self.isa), val)
                        } else if from.size_bytes(&self.isa) < to.size_bytes(&self.isa) {
                            func.ins()
                                .sextend(to.clone().into_cranelift(&self.isa), val)
                        } else {
                            val
                        };

                        Ok((casted, to))
                    }
                    (from, to) => Err(Box::new([CompilationError::InvalidCast(
                        self.file_path.clone(),
                        trace.clone(),
                        Rc::new(from) as Rc<dyn CompilationType>,
                        Rc::new(to) as Rc<dyn CompilationType>,
                    )])),
                }
            }
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
            } => Ok(self
                .compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?
                .0
                .unwrap()),
            AstNode::MatchExpr { matchee, arms } => Ok(self.compile_match(matchee, arms, func, trace)?.unwrap()),
            node => unimplemented!("Compile node {node}"),
        }
    }

    pub fn compile_while_expr(
        &mut self,
        cond_node: &AstNode,
        code: &ParseBlock,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(), Box<[CompilationError]>> {
        let body_block = func.create_block();
        let end_block = func.create_block();

        func.ins().jump(body_block, &[]);
        func.switch_to_block(body_block);

        let ParseBlock::Plain(code) = code;
        let (_, filled) = self.compile_while_body(code.as_ref(), func, trace, end_block, &[])?;

        if !filled {
            let (cond, _) = self.compile_body_expr(cond_node, func, trace)?;
            func.ins().brif(cond, body_block, &[], end_block, &[]);
        }

        func.switch_to_block(end_block);
        func.seal_block(body_block);
        func.seal_block(end_block);

        Ok(())
    }

    pub fn compile_for_in_expr(
        &mut self,
        r#for: &String,
        r#in: &AstNode,
        body: &ParseBlock,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(), Box<[CompilationError]>> {
        let body_block = func.create_block();
        let end_block = func.create_block();

        let (loop_in, lity) = self.compile_body_expr(r#in, func, trace)?;

        assert!(lity.iterable());

        let inner = lity.inner().unwrap();

        self.var_builder.create_scope();

        func.append_block_param(body_block, Type::Int64.into_cranelift(&self.isa));

        let offset = func.ins().iconst(Type::Int64.into_cranelift(&self.isa), 0);

        func.ins().jump(body_block, &[offset]);
        func.switch_to_block(body_block);

        let ParseBlock::Plain(code) = body;

        if matches!(lity, Type::CStr | Type::UCStr) {
            let offset = func.block_params(body_block)[0];
            let ptr = func.ins().iadd(loop_in, offset);

            let current = func.ins().load(
                inner.downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa),
                self.var_builder.flags,
                ptr,
                0
            );

            self.var_builder.create_var(func, current, inner.downcast_ref::<CraneliftType>().unwrap().clone(), r#for.clone(), true);

            self.compile_body(code, func, trace)?;

            let new_offset = func.ins().iadd_imm(offset, inner.size_bytes(&self.isa) as i64);
            let cond = func.ins().icmp_imm(IntCC::NotEqual, current, 0);
            func.ins().brif(cond, body_block, &[new_offset], end_block, &[]);
        } else if matches!(lity, Type::FatPtr(_)) {
            let len = func.ins().load(
                Type::Int32.into_cranelift(&self.isa),
                self.var_builder.flags,
                loop_in,
                0
            );
            
            let one = func.ins().iconst(Type::Int32.into_cranelift(&self.isa), 1);
            let len = func.ins().isub(len, one);

            let offset = func.block_params(body_block)[0];
            let binding = func.ins().udiv_imm(offset, inner.size_bytes(&self.isa) as i64);
            let index = func.ins().ireduce(Type::Int32.into_cranelift(&self.isa), binding);
            let ptr = func.ins().iadd(loop_in, offset);

            let current = func.ins().load(
                inner.downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa),
                self.var_builder.flags,
                ptr,
                4
            );

            self.var_builder.create_var(func, current, inner.downcast_ref::<CraneliftType>().unwrap().clone(), r#for.clone(), true);

            self.compile_body(code, func, trace)?;

            let new_offset = func.ins().iadd_imm(offset, inner.size_bytes(&self.isa) as i64);
            let cond = func.ins().icmp(IntCC::UnsignedLessThan, index, len);
            func.ins().brif(cond, body_block, &[new_offset], end_block, &[]);
        } else {
            unimplemented!("For loops over {in}")
        }

        func.seal_block(body_block);

        func.switch_to_block(end_block);
        func.seal_block(end_block);

        Ok(())
    }

    pub fn compile_body(
        &mut self,
        body: &[AstNode],
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Option<(Value, Type)>, bool), Box<[CompilationError]>> {
        let mut r = (None, false);
        let mut errors = vec![];

        for (i, stmt) in body.iter().enumerate() {
            let res = match stmt {
                AstNode::IfExpr {
                    cond,
                    block,
                    else_clause,
                } => self.compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?,
                AstNode::LetStmt {
                    name,
                    def_type,
                    value,
                } => {
                    let (val, vty) =
                        self.compile_body_expr(value, func, &trace.nested_ctx(ContextKind::Def))?;

                    let ty = if let Some(dty) = def_type {
                        self.tg.compile_type_no_tgs(dty, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone()
                    } else {
                        vty
                    };

                    self.var_builder.create_var(
                        func,
                        val,
                        ty.clone(),
                        name.clone(),
                        true,
                    );

                    (None, false)
                }
                AstNode::MutStmt {
                    name,
                    def_type,
                    value,
                } => {
                    let (val, vty) =
                        self.compile_body_expr(value, func, &trace.nested_ctx(ContextKind::Def))?;

                    let ty = if let Some(dty) = def_type {
                        self.tg.compile_type_no_tgs(dty, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone()
                    } else {
                        vty
                    };

                    self.var_builder.create_var(
                        func,
                        val,
                        ty.clone(),
                        name.clone(),
                        false,
                    );

                    (None, false)
                }
                AstNode::IncludeStmt(_) => todo!(),
                AstNode::ExternFn {
                    name,
                    ret_type,
                    args,
                } => {
                    self.compile_extern_fn(name, ret_type, args)?;
                    (None, false)
                }
                AstNode::ReturnStmt(v) => {
                    let (val, _) = self.compile_body_expr(v, func, trace)?;

                    let mut sig = Signature::new(self.call_conv);

                    sig.params.push(AbiParam::new(self.isa.pointer_type()));
                    sig.returns
                        .push(AbiParam::new(Type::Null.into_cranelift(&self.isa)));

                    let core_msc_free = self
                        .module
                        .declare_function("free", Linkage::Import, &sig)
                        .unwrap();
                    let core_msc_free_fn =
                        self.module.declare_func_in_func(core_msc_free, func.func);

                    if let Some(popped) = self.auto_frees.pop() {
                        // free auto_frees
                        for auto_free in popped {
                            // call core_msc_free(auto_free)
                            func.ins().call(core_msc_free_fn, &[auto_free]);
                        }
                    }

                    if let Some(deferred) = self.deferred_items.pop() {
                        for item in deferred {
                            let ParseBlock::Plain(code) = item;

                            self.compile_body(&code, func, trace)?;
                        }
                    }

                    func.ins().return_(&[val]);
                    func.seal_all_blocks();

                    (None, true)
                }
                AstNode::WhileStmt { cond, code } => {
                    self.compile_while_expr(cond.as_ref(), code, func, trace)?;
                    (None, false)
                }
                AstNode::ForInStmt { var, of, block } => {
                    self.compile_for_in_expr(var, of, block, func, trace)?;
                    (None, false)
                },
                AstNode::IfStmt { cond, block } => (
                    None,
                    self.compile_if_stmt(cond.as_ref(), block, func, None, &[], trace)?,
                ),
                AstNode::DeferStmt(code) => {
                    if let Some(scope) = self.deferred_items.last_mut() {
                        scope.insert(0, code.clone());
                    } else {
                        self.deferred_items.push(vec![code.clone()]);
                    }

                    (None, false)
                }
                AstNode::MatchExpr { matchee, arms } => (self.compile_match(matchee, arms, func, trace)?, false),
                _ => (
                    Some(match self.compile_body_expr(stmt, func, trace) {
                        Ok(v) => v,
                        Err(e) => {
                            errors.extend(e);
                            continue;
                        }
                    }),
                    false,
                ),
            };

            if i == body.len() - 1 {
                r = res
            }
        }

        if errors.len() != 0 {
            return Err(errors.into_boxed_slice());
        }

        Ok(r)
    }

    pub fn compile_while_body(
        &mut self,
        body: &[AstNode],
        func: &mut FunctionBuilder,
        trace: &Trace,
        end_block: Block,
        end_args: &[Value],
    ) -> Result<(Option<(Value, Type)>, bool), Box<[CompilationError]>> {
        let mut r = (None, false);

        for (i, stmt) in body.iter().enumerate() {
            let res = match stmt {
                AstNode::Identifier(n) if n == "break" => {
                    func.ins().jump(end_block, end_args);

                    (None, true)
                }
                AstNode::IfStmt { cond, block } => (
                    None,
                    self.compile_if_stmt(cond.as_ref(), block, func, Some(end_block), &[], trace)?,
                ),
                stmt => self.compile_body(&[stmt.clone()], func, trace)?,
            };

            if i == body.len() - 1 {
                r = res
            }
        }

        Ok(r)
    }

    pub fn compile_extern_fn(
        &mut self,
        name: &String,
        ret_type: &ParseType,
        args: &Box<[(String, ParseType, Option<AstNode>)]>,
    ) -> Result<(), Box<[CompilationError]>> {
        let ret_type = self.tg.compile_type_no_tgs(&ret_type, &self.isa);
        let arg_types = args
            .iter()
            .map(|(_, ty, _)| self.tg.compile_type_no_tgs(ty, &self.isa))
            .collect::<Vec<_>>();

        let mut sig = Signature::new(self.call_conv);

        sig.returns
            .push(AbiParam::new(ret_type.downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa)));
        sig.params.extend(
            arg_types
                .iter()
                .map(|ty| AbiParam::new(ty.downcast_ref::<CraneliftType>().unwrap().clone().into_cranelift(&self.isa))),
        );

        self.module
            .declare_function(name, Linkage::Import, &sig)
            .unwrap();

        self.fn_counter += 1;

        let arg_meta = args
            .iter()
            .map(|(n, ty, _)| (n.clone(), self.tg.compile_type_no_tgs(ty, &self.isa)))
            .collect::<Vec<_>>();

        if let Some(variants) = self.function_variants.get_mut(name) {
            variants.push((ret_type.downcast_ref::<CraneliftType>().unwrap().clone(), arg_types.iter().map(|a| a.downcast_ref::<CraneliftType>().unwrap().clone()).collect::<Vec<_>>()))
        } else {
            self.function_variants
                .insert(name.clone(), vec![(ret_type.downcast_ref::<CraneliftType>().unwrap().clone(), arg_types.iter().map(|a| a.downcast_ref::<CraneliftType>().unwrap().clone()).collect::<Vec<_>>())]);
        }

        self.functions.insert(
            name.clone(),
            FunctionMeta {
                modifiers: vec![].into_boxed_slice(),
                arity: args.len(),
                arg_meta: arg_meta.into_iter().map(|(a, b)| (a.clone(), Rc::from(b))).collect::<Vec<_>>(),
                return_type: Rc::from(ret_type),
                sig,
                index: self.fn_counter,
                auto_free_idx: None,
                start_block: None,
            },
        );

        Ok(())
    }

    pub fn compile_array(&mut self, array: &[AstNode], func: &mut FunctionBuilder, trace: &Trace) -> Result<StackSlot, Box<[CompilationError]>> {
        let mut values = vec![];

        for node in array {
            values.push(self.compile_body_expr(node, func, trace)?);
        }

        let (_, inner_type) = values.first().unwrap();

        let slot = func.create_sized_stack_slot(StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: (inner_type.size_bytes(&self.isa) as usize * array.len()) as u32,
            align_shift: 0,
        });

        for (index, node) in array.iter().enumerate() {
            let bytes = inner_type.size_bytes(&self.isa);

            let (value, _) = self.compile_body_expr(node, func, trace)?;

            func.ins().stack_store(value.clone(), slot, (index * bytes as usize) as i32);
        }

        Ok(slot)
    }

    /// Returns a global value containing the string
    pub fn make_string(
        &mut self,
        string: &String,
        func: &mut FunctionBuilder,
    ) -> Result<GlobalValue, Box<[CompilationError]>> {
        let string_dat = self
            .module
            .declare_data(
                &format!("str${}", self.counter),
                Linkage::Local,
                false,
                false,
            )
            .unwrap();

        self.counter += 1;

        let string = string.replace("\\\"", "\"").replace("\\\\", "\\");
        let string = string.replace("\\0", "\0");
        let string = string.replace("\\red", &"".red().to_string());
        let string = string
            .replace("\\n", "\n")
            .replace("\\t", "\t")
            .replace("\\r", "\r");

        let mut desc = DataDescription::new();
        desc.define(string.into_boxed_str().into_boxed_bytes());

        self.module.define_data(string_dat, &desc).unwrap();

        Ok(self.module.declare_data_in_func(string_dat, func.func))
    }

    /// Returns a pointer to a string
    pub fn compile_string(
        &mut self,
        string: &String,
        func: &mut FunctionBuilder,
    ) -> Result<(Value, Type), Box<[CompilationError]>> {
        let global = self.make_string(string, func)?;

        Ok((
            func.ins().global_value(self.isa.pointer_type(), global),
            Type::Slice(Indirection::new(Type::Int8), string.len() as u32),
        ))
    }

    fn get_calls_of_func(
        &mut self,
        name: &String,
        remaining_nodes: Vec<AstNode>,
    ) -> Result<Vec<Box<[Type]>>, Box<[CompilationError]>> {
        let usages = get_usages_of(name, remaining_nodes.as_slice());
        let calls = usages[1..]
            .into_iter()
            .filter(|usage| matches!(usage.kind, UsageKind::Call(_)))
            .collect::<Vec<_>>();

        if calls.len() == 0 {
            return Ok(vec![]);
        }

        Ok(vec![])
    }

    pub fn compile_func(&mut self, node: &AstNode) -> Result<(), Box<[CompilationError]>> {
        let AstNode::FnStmt {
            of,
            name: unmangled_name,
            ret_type,
            args,
            type_generics: _,
            code,
            modifiers,
        } = node
        else {
            unreachable!();
        };

        let ret_type = self.tg.compile_type_no_tgs(&ret_type, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone();
        let arg_types = args
            .iter()
            .map(|(_, ty, _)| self.tg.compile_type_no_tgs(ty, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone())
            .collect::<Vec<_>>();

        let mangled_name = if modifiers.contains(&Modifier::NoMangle) || &**unmangled_name == "main" {
            unmangled_name.clone()
        } else if let Some(of) = of {
            mangle_method(of, unmangled_name, &arg_types, &ret_type)
        } else {
            mangle_function(unmangled_name, &arg_types, &ret_type)
        };

        let mut sig = Signature::new(self.call_conv);

        sig.returns
            .push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
        sig.params.extend(
            arg_types
                .iter()
                .map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))),
        );

        let ParseBlock::Plain(code) = code;

        let linkage = if unmangled_name == "main" || modifiers.contains(&Modifier::Export) {
            Linkage::Export
        } else {
            Linkage::Local
        };

        let name = &mangled_name;

        let mut auto_free_idx = None;

        if modifiers.contains(&Modifier::AutoFree) {
            self.auto_frees.push(HashSet::new());
            auto_free_idx = Some(self.auto_frees.len() - 1);
        }

        let fid = self.module.declare_function(&name, linkage, &sig).unwrap();

        self.fn_counter += 1;

        let mut func =
            Function::with_name_signature(UserFuncName::user(0, fid.index() as u32), sig.clone());
        
        self.fn_refs.insert(mangled_name.clone(), (func.clone(), fid));

        let mut ctx = FunctionBuilderContext::new();

        let mut fn_builder = FunctionBuilder::new(&mut func, &mut ctx);

        if modifiers.contains(&Modifier::Alloc) {
            self.allocator_fns.insert(name.clone());
        } else if modifiers.contains(&Modifier::Dealloc) {
            self.deallocator_fns.insert(name.clone());
        }

        let arg_meta = args
            .iter()
            .map(|(n, ty, _)| (n.clone(), self.tg.compile_type_no_tgs(ty, &self.isa)))
            .collect::<Vec<_>>();

        let block = fn_builder.create_block();

        fn_builder.append_block_params_for_function_params(block);

        fn_builder.switch_to_block(block);
        fn_builder.seal_block(block);

        if let Some(variants) = self.function_variants.get_mut(name) {
            variants.push((ret_type.clone(), arg_types.clone()))
        } else {
            self.function_variants.insert(
                unmangled_name.clone(),
                vec![(ret_type.clone(), arg_types.clone())],
            );
        }

        self.functions.insert(
            name.clone(),
            FunctionMeta {
                auto_free_idx,
                modifiers: modifiers.clone(),
                arity: args.len(),
                arg_meta: arg_meta.into_iter().map(|(a, b)| (a.clone(), Rc::from(b))).collect::<Vec<_>>(),
                return_type: Rc::new(ret_type),
                sig,
                index: self.fn_counter,
                start_block: Some(block),
            },
        );

        let mut trace = Trace::new_root(name.clone());

        self.var_builder.create_scope();

        for (i, (arg_name, arg_type, _)) in args.iter().enumerate() {
            let p = fn_builder.block_params(block)[i];
            let ty = self.tg.compile_type_no_tgs(arg_type, &self.isa).downcast_ref::<CraneliftType>().unwrap().clone();

            self.var_builder.create_var(
                &mut fn_builder,
                p,
                ty,
                arg_name.clone(),
                true,
            );
        }

        self.compile_body(code.as_ref(), &mut fn_builder, &mut trace)?;

        fn_builder.finalize();

        let mut context = Context::for_function(func.clone());

        if &*name == "main" {
            if self.must_frees.len() != 0 {
                let mut errors = vec![];

                for item in self.must_frees.iter() {
                    errors.push(CompilationError::NotFreed(
                        self.file_path.clone(),
                        trace.clone(),
                        item.clone(),
                    ))
                }

                return Err(errors.into_boxed_slice());
            }
        }

        self.module.define_function(fid, &mut context).unwrap();

        Ok(())
    }

    pub fn compile_global(&mut self, node: &AstNode) -> Result<(), Box<[CompilationError]>> {
        match node {
            AstNode::FnStmt { .. } => self.compile_func(node),
            AstNode::ExternFn {
                name,
                ret_type,
                args,
            } => self.compile_extern_fn(name, ret_type, args),
            AstNode::IncludeStmt(p) => {
                let search_path = p.as_ref().split_last().unwrap().1.join("/");
                let parent_path = self
                    .file_path
                    .parent()
                    .unwrap()
                    .to_string_lossy()
                    .to_string();

                let mut msc_path: PathBuf = [search_path.clone(), format!("{}.msc", p.last().unwrap())].iter().collect();

                let mut obj_path: Option<PathBuf> = Some(PathBuf::from(format!(
                    "./{search_path}/{}.o",
                    p.last().unwrap()
                )));

                // Attempt lookup in installed modules directory (~/.msc/mods/)
                if !msc_path.exists() {
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

                if self
                    .included_modules
                    .iter()
                    .any(|m| m.mosaic_file == msc_path)
                {
                    return Ok(());
                }

                if let Some(ref p) = obj_path {
                    if !p.exists() {
                        obj_path = None;
                    }
                }

                if !msc_path.exists() {
                    return Err(Box::new([CompilationError::UnknownModule(
                        self.file_path.clone(),
                        Trace::new_root("GLOBAL".to_string()),
                        p.clone(),
                    )]));
                }

                // SHADOW CODEGEN

                let reader =
                    CharReader::new(File::new(msc_path.to_str().unwrap().to_string()).unwrap());

                let lexer = StreamedLexer::new(reader);
                let parser = StreamedParser::new(lexer);

                // Compile the module and add it to the included modules.

                let shadow_cg = Self::new(
                    parser,
                    isa::lookup(self.isa_builder.triple().clone()).unwrap(),
                    None,
                );

                let gen = shadow_cg.compile(true, obj_path.clone())?;

                self.tg.merge(&gen.tg);
                self.included_modules.push(gen);

                Ok(())
            }
            AstNode::TypeAlias(name, to) => {
                let to = self.tg.compile_type_no_tgs(to, &self.isa);

                self.tg.register_type(name, to);

                Ok(())
            }
            n => unimplemented!("Global compilation of {n:?}"),
        }
    }

    pub fn compile(
        mut self,
        write: bool,
        assoc_obj: Option<PathBuf>,
    ) -> Result<CraneliftModule, Box<[CompilationError]>> {
        let mut errors = vec![];
        let mut nodes = vec![];

        for node in self.parser.iter() {
            match node {
                Ok(n) => nodes.push(n),
                Err(e) => errors.push(e),
            }
        }

        let mut engine = PreoptEngine::new(&nodes);

        //engine.removed_unused_defs();
        engine.demote_mutables();

        //let nodes = engine.finish();

        for node in nodes {
            match self.compile_global(&node) {
                Ok(_) => (),
                Err(e) => errors.extend(e),
            };
        }

        let res = self.module.finish();

        let mut out_file = self.file_path.clone();

        if let Some(Command::Build {
            out_file: Some(dest),
            ..
        }) = self.command.clone()
        {
            out_file.set_file_name(dest);
        } else {
            out_file.set_file_name(format!("{M}.cmp.o", M = self.module_name));
        }

        if write {
            let mut file = fs::File::create(out_file.clone()).unwrap();
            res.object.write_stream(&mut file).unwrap();
        }

        let prev_includes = self
            .included_modules
            .iter()
            .flat_map(|m| {
                [
                    m.prev_includes.clone().into_iter().collect(),
                    vec![(m.mosaic_file.clone(), m.assoc_obj.clone())],
                ]
                .into_iter()
                .flatten()
            })
            .collect::<Vec<_>>();

        if errors.len() > 0 {
            return Err(errors.into());
        }

        Ok(CraneliftModule {
            product: res,
            assoc_obj,
            name: self.module_name,
            prev_includes: HashSet::from_iter(prev_includes),
            mosaic_file: self.file_path,
            functions: self.functions,
            function_variants: self.function_variants,
            tg: self.tg,
            out_file,
        })
    }

    fn compile_if_expr(
        &mut self,
        cond: &AstNode,
        code: &ParseBlock,
        else_code: &ParseBlock,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(Option<(Value, CraneliftType)>, bool), Box<[CompilationError]>> {
        let success_block = func.create_block();
        let else_block = func.create_block();
        let end_block = func.create_block();

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;

        func.ins().brif(cond, success_block, &[], else_block, &[]);

        /**** success ****/

        func.switch_to_block(success_block);

        let ParseBlock::Plain(code) = code;

        // TODO: If statements with else clauses
        let (Some((res, res_ty)), filled) = self.compile_body(code.as_ref(), func, trace)? else {
            func.ins().jump(end_block, &[]);

            /**** failure ****/

            func.switch_to_block(else_block);

            let ParseBlock::Plain(else_code) = else_code;
            let (_, filled) = self.compile_body(else_code.as_ref(), func, trace)?;

            func.ins().jump(end_block, &[]);

            func.switch_to_block(end_block);

            func.seal_block(success_block);
            func.seal_block(else_block);
            func.seal_block(end_block);

            return Ok((None, filled));
        };

        func.append_block_param(end_block, res_ty.clone().into_cranelift(&self.isa));

        if !filled {
            func.ins().jump(end_block, &[res]);
        }

        /**** failure ****/

        func.switch_to_block(else_block);

        let ParseBlock::Plain(else_code) = else_code;
        let (Some((res, _)), _) = self.compile_body(else_code.as_ref(), func, trace)? else {
            func.switch_to_block(end_block);

            return Ok((None, filled));
        };

        func.ins().jump(end_block, &[res]);

        func.switch_to_block(end_block);

        func.seal_block(success_block);
        func.seal_block(else_block);
        func.seal_block(end_block);

        let result = func.block_params(end_block)[0];

        Ok((Some((result, res_ty)), filled))
    }

    fn compile_match(
        &mut self,
        matchee: &AstNode,
        arms: &[MatchArm],
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<Option<(Value, Type)>, Box<[CompilationError]>> {
        // create the necessary blocks (for arms, else, and end)

        let end_block = func.create_block();

        let mut arm_blocks = vec![];

        for _ in arms {
            arm_blocks.push(func.create_block());
        }

        let mut result_type = None;

        // jump to the first arm block

        func.ins().jump(arm_blocks[0], &[]);

        let else_block = arm_blocks.last().unwrap();

        // compile the arms
        
        let (left_part, right_part): (Vec<_>, Vec<_>) = arms.iter().enumerate().map(|(i, arm)| (i, (arm, arm_blocks[i]))).partition(|(_, (arm, _))| arm.is_else);
        let combined = [&*left_part, &*right_part].concat();
        
        for (i, (arm, block)) in combined {
            // the previous block will be filled,
            // so we can just switch to this arm's block.

            func.switch_to_block(block);

            // then we compile the condition
            // and break to the appropriate block,
            // which is the next arm block (not else), else block (last arm),
            // or end block (no break needed)

            if !arm.is_else {
                let code_block = func.create_block();

                let (cond, _) = self.compile_cmp_op(&arm.operator, matchee, &arm.right, func, trace)?;

                // we need to create a code block (due to how cranelift handles condition jumps)

                if i != arms.len() - 2 {
                    // this is neither the else arm, nor the last arm,
                    // so we break to the code or next arm block.

                    func.ins().brif(cond, code_block, &[], arm_blocks[i + 1], &[]);
                } else {
                    // this is not the else arm, but is the last arm,
                    // so we break to the code or else block.

                    func.ins().brif(cond, code_block, &[], *else_block, &[]);
                }

                // compile the arm's code

                func.switch_to_block(code_block);

                let ParseBlock::Plain(ref code) = arm.code;

                // TODO: check for required value
                let (result, filled) = self.compile_body(code.as_ref(), func, trace)?;

                if result.clone().map(|v| v.1) != result_type {
                    todo!("Handle error properly here (invalid result type for match arm)")
                }

                if !filled {
                    if let Some((val, _)) = result {
                        func.ins().jump(end_block, &[val]);
                    } else {
                        func.ins().jump(end_block, &[]);
                    }
                }
            } else {
                // compile the arm's code

                let ParseBlock::Plain(ref code) = arm.code;

                let (result, filled) = self.compile_body(code.as_ref(), func, trace)?;

                // TODO: check for required value
                result_type = result.clone().map(|v| v.1);

                if !filled {
                    if let Some((val, ty)) = result {
                        func.append_block_param(end_block, ty.into_cranelift(&self.isa));

                        func.ins().jump(end_block, &[val]);
                    } else {
                        func.ins().jump(end_block, &[]);
                    }
                }
            }
        }

        func.switch_to_block(end_block);

        if let Some(ty) = result_type {
            Ok(Some((func.block_params(end_block)[0], ty)))
        } else {
            Ok(None)
        }
    }

    // TODO: If statements \w else clauses
    fn compile_if_stmt(
        &mut self,
        cond: &AstNode,
        code: &ParseBlock,
        func: &mut FunctionBuilder,
        while_end_block: Option<Block>,
        while_end_args: &[Value],
        trace: &Trace,
    ) -> Result<bool, Box<[CompilationError]>> {
        let success_block = func.create_block();
        let end_block = func.create_block();

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;

        func.ins().brif(cond, success_block, &[], end_block, &[]);

        /**** success ****/

        func.switch_to_block(success_block);

        let ParseBlock::Plain(code) = code;

        let (_, filled) = if let Some(block) = while_end_block {
            self.compile_while_body(code.as_ref(), func, trace, block, while_end_args)?
        } else {
            self.compile_body(code.as_ref(), func, trace)?
        };

        if !filled {
            func.ins().jump(end_block, &[]);
        }

        func.switch_to_block(end_block);

        Ok(filled)
    }
}
