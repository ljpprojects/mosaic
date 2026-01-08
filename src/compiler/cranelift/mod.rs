#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![forbid(unsafe_code)]

use crate::compiler::analyser::{UsageKind, get_usages_of};
use crate::compiler::cranelift::ast::flatten_ast;
use crate::compiler::traits::CompilationModule;
pub mod builders;
pub mod linker;
pub mod mangle;
pub mod meta;
pub mod module;
pub mod trace;
pub mod types;
pub mod value;
pub mod ast;

use crate::cli::Command;
use crate::compiler::cranelift::builders::VariableBuilder;
use crate::compiler::cranelift::mangle::{mangle_function, mangle_method, mangle_type};
use crate::compiler::cranelift::meta::{DataDeclMeta, FunctionMeta, MustFreeMeta};
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
use cranelift_codegen::ir::{AbiParam, Block, BlockArg, ExtFuncData, ExternalName, FuncRef, Function, GlobalValue, GlobalValueData, InstBuilder, MemFlags, Signature, StackSlot, StackSlotData, StackSlotKind, UserExternalName, UserExternalNameRef, UserFuncName, Value};
use cranelift_codegen::isa::{Builder, CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::Configurable;
use cranelift_codegen::{ir, isa, settings, Context};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{default_libcall_names, DataDescription, FuncId, Init, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use crate::compiler::align::{alignment_of_cranelift_type_on_architecture, calculate_data_cranelift};
use crate::compiler::indexing::FileIndexer;
use crate::ternary;

macro_rules! get_fn {
    ($self:expr, $name:expr) => {
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

                res.map(|v| v.iter().map(|(a, b)| (a.clone(), b.iter().cloned().collect::<Vec<_>>())).collect::<Vec<_>>())
            }
        }
    };
}

pub struct CraneliftGenerator {
    /// A counter for unique names.
    counter: usize,

    /// The name of the module that is being compiled.
    module_name: String,

    /// The amount functions that have been compiled so far in this module.
    fn_counter: u32,

    /// The path to the Mosaic file being compiled.
    file_path: PathBuf,

    /// The parser.
    parser: StreamedParser,

    /// Every variant of the compiled functions.
    function_variants: HashMap<String, Vec<(CraneliftType, Vec<CraneliftType>)>>,

    /// A map of mangled function names to their metadata.
    functions: HashMap<String, FunctionMeta>,

    /// A map of data declarations to their metadata.
    data_declarations: HashMap<String, DataDeclMeta>,

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

    /// A list of every module that the current module (or previous modules referencing it) has included.
    included_modules: BTreeSet<CraneliftModule>,

    /// A set of module names that are currently being compiled AND SHOULD NOT GET RECOMPILED
    compiling_list: BTreeSet<String>,

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

    nodes: Vec<AstNode>,

    //Indexer: FileIndexer,
}

impl CraneliftGenerator {
    pub fn new(parser: StreamedParser, isa_builder: Builder, command: Option<Command>, previously_included_mods: Option<BTreeSet<CraneliftModule>>, previously_compiling: Option<BTreeSet<String>>) -> Self {
        let file_path: PathBuf = if let Some(Command::Build { file, .. }) = command.clone() {
            file.into()
        } else {
            parser.lexer.reader.reader.path().into()
        };

        let mut shared_builder = settings::builder();

        shared_builder.enable("is_pic").unwrap();
        shared_builder.enable("enable_alias_analysis").unwrap();
        shared_builder.set("opt_level", "speed").unwrap();
        shared_builder.set("regalloc_algorithm", "backtracking").unwrap();

        let shared_flags = settings::Flags::new(shared_builder);

        let isa = isa_builder.finish(shared_flags).unwrap();

        let call_conv = isa.default_call_conv();

        let module_name = file_path.file_stem().unwrap().to_str().unwrap().to_string();

        let mut obj_builder =
            ObjectBuilder::new(isa.clone(), module_name.clone(), default_libcall_names()).unwrap();

        let mut module = ObjectModule::new(obj_builder);

        let tag_data = module.declare_data("INFO", Linkage::Local, false, false).unwrap();

        let mut desc = DataDescription::new();
        desc.define(Box::from("LOL THIS FUCKING IDIOT USED MOSAIC".as_bytes()));

        module.define_data(tag_data, &desc).unwrap();

        let mut compiling_list = previously_compiling.unwrap_or_default();
        compiling_list.insert(module_name.clone());

        Self {
            counter: 0,
            module_name,
            file_path,
            parser,
            function_variants: Default::default(),
            functions: Default::default(),
            data_declarations: Default::default(),
            var_builder: VariableBuilder::new(&isa),
            module,
            call_conv,
            isa,
            fn_counter: 0,
            isa_builder,
            tg: CraneliftTypeGenerator::new(),
            included_modules: previously_included_mods.unwrap_or_default(),
            compiling_list,
            auto_frees: vec![],
            deferred_items: vec![],
            allocator_fns: HashSet::new(),
            deallocator_fns: HashSet::new(),
            must_frees: HashSet::new(),
            command,
            fn_refs: HashMap::new(),
            nodes: vec![],
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
                match left {
                    AstNode::Identifier(_, name) => {
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
                    AstNode::IdxAccess(_, of, idx) => {
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

                        Ok((right, rty))
                    }
                    AstNode::PrefixOp(_, op, val) if &**op == "*" => {
                        let (addr, _) = self.compile_body_expr(val, func, trace)?;
                        let (right, rty) = self.compile_body_expr(right, func, trace)?;

                        // TODO: Type checking

                        func.ins()
                            .store(self.var_builder.flags, right, addr, 0);

                        Ok((right, rty))
                    }
                    AstNode::MemberExpr(_, root, prop) => {
                        let (ptr, pty) = self.compile_body_expr(root, func, trace)?;

                         let (right, rty) = self.compile_body_expr(right, func, trace)?;

                        let pty = match pty {
                            Type::Declared(_, inner) => inner.deref().clone(),
                            ty => ty
                        };

                        let Type::DataPtr(name) = pty else {
                            todo!("Handle error case: invalid member access type: {pty:?}")
                        };

                        let meta = self.data_declarations.get(&name).unwrap();
                        let Some((offset, _, _, ty)) = meta.fields.iter().find(|(_, _, name, _)| name == prop) else {
                            todo!("Handle error case: field does not exist in member assignment")
                        };

                        let ty = ty.clone();

                        if rty != ty {
                            todo!("Handle error case: invalid type")
                        }

                        let data = StackSlotData {
                            key: None,
                            kind: StackSlotKind::ExplicitSlot,
                            size: rty.size_bytes(&self.isa) as u32,
                            align_shift: 0
                        };

                        let slot = func.create_sized_stack_slot(data);
                        let size = func.ins().iconst(ir::types::I32, rty.size_bytes(&self.isa) as i64);
                        let addr = func.ins().stack_addr(self.isa.pointer_type(), slot, *offset as i32);

                        let mut sig = self.module.make_signature();

                        sig.params.extend([AbiParam::new(self.isa.pointer_type()), AbiParam::new(self.isa.pointer_type()), AbiParam::new(ir::types::I32)]);

                        let fid = self.module.declare_function("memcpy", Linkage::Import, &sig).unwrap();
                        let memcpy = self.module.declare_func_in_func(fid, func.func);

                        func.ins().call(memcpy, &[ptr, addr, size]);

                        Ok((right, rty))
                    }
                    _ => todo!("Handle error case: cannot assign to {left}")
                }
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

                if !lty.cmp_eq(&rty) {
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

                if !lty.cmp_eq(&rty) {
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
            "||" => {
                let (left, _) = self.compile_body_expr(left, func, trace)?;
                let (right, _) = self.compile_body_expr(right, func, trace)?;

                //let left = func.ins().sextend(ir::types::I32, left);
                let right = func.ins().sextend(ir::types::I32, right);

                Ok((func.ins().bor(left, right), Type::Bool))
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
                    (func.ins().fadd(left, right), lty)
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
                    (func.ins().fmul(left, right), lty)
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
                    (func.ins().urem(left, right), lty.to_unsigned().unwrap())
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
                match right {
                    AstNode::MemberExpr(_, root, prop) => {
                        let (ptr, pty) = self.compile_body_expr(root, func, trace)?;

                        let pty = match pty {
                            Type::Declared(_, inner) => inner.deref().clone(),
                            ty => ty
                        };

                        let Type::DataPtr(name) = pty.clone() else {
                            todo!("Handle error case: invalid member access type: {pty:?}")
                        };

                        let meta = self.data_declarations.get(&name).unwrap();
                        let Some((offset, _, _, ty)) = meta.fields.iter().find(|(_, _, name, _)| name == prop) else {
                            todo!("Handler error case: field does not exist in member access")
                        };

                        let offset_ptr = func.ins().iadd_imm(ptr, *offset as i64);

                        Ok((offset_ptr, pty))
                    },
                    AstNode::Identifier(_, name) => {
                        let (ptr, ty, mutable) =
                            self.var_builder
                                .get_var_ptr(func, name, self.file_path.clone(), trace)?;

                        Ok((ptr, Type::CPtr(Indirection::new(ty), mutable, false)))
                    }
                    _ => Err(Box::new([CompilationError::UndefinedOperator(self.file_path.clone(), trace.clone(), "& (on an expression)".to_string())]))
                }
            }
            "*" => {
                let (ptr, pty) = self.compile_body_expr(right, func, trace)?;

                let value = func.ins().load(
                    pty.inner().unwrap().into_cranelift(&self.isa),
                    self.var_builder.flags,
                    ptr,
                    0,
                );

                Ok((value, pty.inner().unwrap()))
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
            AstNode::SizeOf(_, ty) => Ok((
                func.ins().iconst(Type::Int32.into_cranelift(&self.isa), self.tg.compile_type_no_tgs(ty, &self.isa).size_bytes(&self.isa) as i64),
                Type::UIntSize
            )),
            AstNode::NumberLiteral(_l, i) if i.fract() == 0f64 => {
                let ty = Type::Int32;

                Ok((func.ins().iconst(ir::types::I32, Imm64::new(*i as i64)), ty))
            }
            AstNode::NumberLiteral(_l, i) => Ok((func.ins().f64const(*i), Type::Float64)),
            AstNode::ByteLiteral(_l, b) => Ok((
                func.ins().iconst(ir::types::I8, Imm64::new(*b as i64)),
                Type::Int8,
            )),
            AstNode::StringLiteral(_l, s) => self.compile_string(s, func),
            AstNode::ArrayLiteral(_l, a) => {
                let r = self.compile_array(a, func, trace)?;

                Ok((r.1, r.2))
            },

            AstNode::BooleanLiteral(_, b) => {
                Ok((func.ins().iconst(ir::types::I8, Imm64::new(ternary!(*b => 1; 0))), Type::Bool))
            }

            AstNode::NullLiteral(..) => {
                Ok((func.ins().iconst(ir::types::I8, Imm64::new(0)), Type::Null))
            }
            AstNode::Identifier(_l, i) => {
                Ok(self
                    .var_builder
                    .get_var(func, i, self.file_path.clone(), trace)?)
            }
            AstNode::InfixOp(_l, l, o, r) => self.compile_bit_op(o, l, r, func, trace),
            AstNode::PrefixOp(_l, op, r) => self.compile_prefix_op(op, r, func, trace),
            AstNode::PostfixOp(..) => todo!(),
            AstNode::Path(..) => todo!(),
            AstNode::MemberExpr(_, root, prop) => {
                let (ptr, pty) = self.compile_body_expr(root, func, trace)?;

                let pty = match pty {
                    Type::Declared(_, inner) => inner.deref().clone(),
                    ty => ty
                };

                let Type::DataPtr(name) = pty.clone() else {
                    todo!("Handle error case: invalid member access type: {pty:?}")
                };

                let meta = self.data_declarations.get(&name).unwrap();
                let Some((offset, _, _, ty)) = meta.fields.iter().find(|(_, _, name, _)| name == prop) else {
                    todo!("Handler error case: field does not exist in member access")
                };

                let ty = ty.clone();

                Ok((func.ins().load(ty.clone().into_cranelift(&self.isa), self.var_builder.flags, ptr, *offset as i32), ty))
            },
            AstNode::DataInitExpr { name, fields: raw_fields, line_info } => {
                let mut fields = HashMap::new();

                for (name, v) in raw_fields.iter() {
                    fields.insert(name, self.compile_body_expr(v, func, trace)?);
                }

                if let Some(meta) = self.data_declarations.get(name) {
                    let slot_data = StackSlotData {
                        key: None,
                        kind: StackSlotKind::ExplicitSlot,
                        size: meta.size as StackSize,
                        align_shift: meta.alignment.ilog2() as u8,
                    };

                    let slot = func.create_sized_stack_slot(slot_data);

                    for (offset, _, name, ty) in meta.fields.iter() {
                        let Some((value, vty)) = fields.get(name) else {
                            todo!("Handle invalid field in data initialiser")
                        };

                        if !vty.cmp_eq(&ty) {
                            todo!("Handle type mismatch in data initialiser")
                        }

                        func.ins().stack_store(value.clone(), slot, offset.clone() as i32);
                    }

                    Ok((func.ins().stack_addr(self.isa.pointer_type(), slot, 0), CraneliftType::DataPtr(name.clone())))
                } else {
                    Err(Box::new([CompilationError::UndefinedData(self.file_path.clone(), trace.clone(), name.clone())]))
                }
            }
            AstNode::GuardClause {
                cond,
                else_code: ParseBlock::Plain(else_code),
                ..
            } => {
                let (cond, cty) = self.compile_body_expr(cond.deref(), func, trace)?;
                let check = func.ins().icmp_imm(IntCC::NotEqual, cond, 0);

                let cty = match cty {
                    Type::Declared(_, ty) => ty.deref().clone(),
                    t => t
                };

                if !cty.is_pointer() {
                    todo!("Handle error case: invalid type for guard clause")
                }

                if !cty.nullable() {
                    return Ok((cond, cty))
                }

                let end_block = func.create_block();
                let else_block = func.create_block();

                func.ins().brif(check, end_block, &[], else_block, &[]);
                func.switch_to_block(else_block);

                let (_, filled) = self.compile_body(else_code, func, trace)?;

                if !filled {
                    todo!("Handle error case: guard clause else block falls through")
                }

                func.switch_to_block(end_block);

                let val = cond;

                let new_type = match cty {
                    Type::CPtr(i, m, _) => Type::CPtr(i, m, false),
                    Type::FatPtr(i, m, _) => Type::FatPtr(i, m, false),
                    Type::Slice(i, l, m, _) => Type::Slice(i, l, m, false),
                    _ => unreachable!()
                };

                Ok((val, new_type))
            },
            AstNode::IdxAccess(_l, of, idx) => {
                let (of, ty) = self.compile_body_expr(of, func, trace)?;
                let (mut idx, ity) =
                    self.compile_body_expr(idx, func, &trace.nested_ctx(ContextKind::Idx))?;

                if ity.size_bytes(&self.isa) < self.isa.pointer_bytes() {
                    idx = func.ins().uextend(self.isa.pointer_type(), idx)
                }

                let inner_ty = ty.inner().unwrap();
                let inner_ty_size = inner_ty.size_bytes(&self.isa) as i64;

                let offset = func.ins().imul_imm(idx, inner_ty_size);
                let computed_addr = func.ins().iadd(of, offset);

                Ok((
                    func.ins().load(
                        inner_ty.clone().into_cranelift(&self.isa),
                        MemFlags::trusted().with_checked(),
                        computed_addr,
                        0,
                    ),
                    inner_ty,
                ))
            }
            AstNode::CallExpr { callee, args, .. } => {
                match callee.as_ref() {
                    AstNode::Identifier(_, name) => {
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
                                            .all(|(i, t)| t.cmp_eq(args.get(i).unwrap()))
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

                                let mangled_name = mangle_function(name, &*arg_types, ret_type);

                                let Some(fn_meta) = get_fn!(self, &mangled_name) else {
                                    eprintln!("SIGNATURES of {name} -> {:?}", self.functions.iter().map(|(n, _)| n).collect::<Vec<_>>());

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

                                return Ok((ret, fn_meta.return_type.clone()));
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
                            .cloned()
                            .unwrap_or(func.ins().iconst(ir::types::I8, 0));

                        Ok((ret, fn_meta.return_type.clone()))
                    },

                    AstNode::Path(_, p) => {
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
                                    .all(|(i, t)| t.cmp_eq(args.get(i).unwrap()))
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
                            println!("(mangled = {mangled_name}) fns = {:?}", self.functions.iter().map(|(n, _)| n).collect::<Vec<_>>());

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

                        Ok((ret, fn_meta.return_type.clone()))
                    },

                    AstNode::MemberExpr(_, root, prop) => {
                        let this =
                            self.compile_body_expr(root, func, trace)?;
                        let method_name = prop;

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
                                    .all(|(i, t)| t.cmp_eq(args.get(i).unwrap()))
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
                            &match &this.1 {
                                Type::DataPtr(n) => n.clone(),
                                Type::Declared(name, _) => name.clone(),
                                _ => mangle_type(&this.1)
                            },
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

                        Ok((ret, fn_meta.return_type.clone()))
                    }

                    e => todo!("Handle error case: uncallable expression ({e:?}) called")
                }
            }
            AstNode::AsExpr(_l, val, ty) => {
                let (val, vty) = self.compile_body_expr(val, func, &trace)?;
                let ty = self.tg.compile_type_no_tgs(ty, &self.isa);

                let (name, ty) = match ty {
                    Type::Declared(n, t) => (Some(n), t.deref().clone()),
                    t => (None, t),
                };

                let vty = match vty {
                    Type::Declared(_, t) => t.deref().clone(),
                    t => t,
                };

                if vty == ty {
                    return Ok((val, vty))
                }

                eprintln!("{trace:?}");

                let (v, r) = match (vty.clone(), ty.clone()) {
                    (Type::Int8, Type::Bool) | (Type::UInt8, Type::Bool) => Ok((val, ty)),
                    (Type::Bool, Type::Int8) | (Type::Bool, Type::UInt8) => Ok((val, ty)),
                    (Type::CPtr(i, ..), pty) if pty.is_pointer() && matches!(*i, Type::Any) => Ok((val, ty)),
                    (Type::CPtr(_, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::Slice(_, _, m1, n1), Type::Slice(_, _, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::FatPtr(_, m1, n1), Type::FatPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::Slice(_, _, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::FatPtr(_, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::CPtr(_, m1, n1), Type::FatPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => Ok((val, ty)),
                    (Type::Slice(inner, len, m1, n1), Type::FatPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => {
                        let slot = func.create_sized_stack_slot(StackSlotData {
                            key: None,
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
                    (from, Type::Float32 | Type::Float64) if from.is_numeric() => {
                        if from.is_signed() {
                            Ok((func.ins().fcvt_from_sint(ty.clone().into_cranelift(&self.isa), val), ty))
                        } else {
                            Ok((func.ins().fcvt_from_uint(ty.clone().into_cranelift(&self.isa), val), ty))
                        }
                    }
                    (Type::DataPtr(..), Type::CPtr(inner, ..)) if matches!(inner.deref(), Type::Any) => Ok((val, ty)),
                    (Type::Float32 | Type::Float64, to) if to.is_numeric() => {
                        if to.is_signed() {
                            Ok((func.ins().fcvt_to_sint(to.clone().into_cranelift(&self.isa), val), to))
                        } else {
                            Ok((func.ins().fcvt_to_uint(to.clone().into_cranelift(&self.isa), val), to))
                        }
                    }
                    (Type::IntSize, p) | (Type::UIntSize, p) if p.is_pointer() => Ok((val, ty)),
                    (p, Type::IntSize) | (p, Type::UIntSize) if p.is_pointer() => Ok((val, ty)),
                    (from, to)
                        if (from.is_numeric() || matches!(from, Type::Bool)) && to.is_numeric() =>
                    {
                        let casted = if from.size_bytes(&self.isa) > to.size_bytes(&self.isa) {
                            func.ins()
                                .ireduce(to.clone().into_cranelift(&self.isa), val)
                        } else if from.size_bytes(&self.isa) < to.size_bytes(&self.isa) && to.is_signed() {
                            func.ins()
                                .sextend(to.clone().into_cranelift(&self.isa), val)
                        } else if from.size_bytes(&self.isa) < to.size_bytes(&self.isa) /*implied && !to.is_signed()*/ {
                            func.ins()
                                .uextend(to.clone().into_cranelift(&self.isa), val)
                        } else {
                            val
                        };

                        Ok((casted, to))
                    }
                    (from, to) => Err(Box::new([CompilationError::InvalidCast(
                        self.file_path.clone(),
                        trace.clone(),
                        Rc::new(from) as Rc<dyn CompilationType>,
                        Rc::new(ty) as Rc<dyn CompilationType>,
                    )])),
                }.unwrap();

                if let Some(name) = name {
                    Ok((v, Type::Declared(name, Indirection::new(r))))
                } else {
                    Ok((v, r))
                }
            }
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
                ..
            } => Ok(self
                .compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?
                .0
                .unwrap()),
            AstNode::MatchExpr { matchee, arms, .. } => Ok(self.compile_match(matchee, arms, func, trace)?.unwrap()),
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

        let lity = match lity {
            Type::Declared(_, ty) => ty.deref().clone(),
             t => t,
        };

        assert!(lity.iterable());

        let inner = lity.inner().unwrap();

        self.var_builder.create_scope();

        func.append_block_param(body_block, Type::Int64.into_cranelift(&self.isa));

        let offset = func.ins().iconst(Type::Int64.into_cranelift(&self.isa), 0);

        func.ins().jump(body_block, &[BlockArg::Value(offset)]);
        func.switch_to_block(body_block);

        let ParseBlock::Plain(code) = body;

        if matches!(lity, Type::FatPtr(..)) {
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
                inner.clone().into_cranelift(&self.isa),
                self.var_builder.flags,
                ptr,
                4
            );

            self.var_builder.create_var(func, current, inner.clone(), r#for.clone(), true);

            self.compile_body(code, func, trace)?;

            let new_offset = func.ins().iadd_imm(offset, inner.size_bytes(&self.isa) as i64);
            let cond = func.ins().icmp(IntCC::UnsignedLessThan, index, len);
            func.ins().brif(cond, body_block, &[BlockArg::Value(new_offset)], end_block, &[]);
        } else if let Type::Slice(_, len, ..) = lity {
            let len = func.ins().iconst(Type::Int32.into_cranelift(&self.isa), len as i64);

            let one = func.ins().iconst(Type::Int32.into_cranelift(&self.isa), 1);
            let len = func.ins().isub(len, one);

            let offset = func.block_params(body_block)[0];
            let binding = func.ins().udiv_imm(offset, inner.size_bytes(&self.isa) as i64);
            let index = func.ins().ireduce(Type::Int32.into_cranelift(&self.isa), binding);
            let ptr = func.ins().iadd(loop_in, offset);

            let current = func.ins().load(
                inner.clone().into_cranelift(&self.isa),
                self.var_builder.flags,
                ptr,
                0
            );

            self.var_builder.create_var(func, current, inner.clone(), r#for.clone(), true);

            self.compile_body(code, func, trace)?;

            let new_offset = func.ins().iadd_imm(offset, inner.size_bytes(&self.isa) as i64);
            let cond = func.ins().icmp(IntCC::UnsignedLessThan, index, len);
            func.ins().brif(cond, body_block, &[BlockArg::Value(new_offset)], end_block, &[]);
        } else {
            unimplemented!("For loops over {lity}")
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
                    ..
                } => self.compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?,
                AstNode::LetStmt {
                    name,
                    def_type,
                    value,
                    ..
                } => {
                    let (val, vty) =
                        self.compile_body_expr(value, func, &trace.nested_ctx(ContextKind::Def))?;

                    let ty = if let Some(dty) = def_type {
                        self.tg.compile_type_no_tgs(dty, &self.isa)
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
                    ..
                } => {
                    let (val, vty) =
                        self.compile_body_expr(value, func, &trace.nested_ctx(ContextKind::Def))?;

                    let ty = if let Some(dty) = def_type {
                        self.tg.compile_type_no_tgs(dty, &self.isa)
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
                AstNode::IncludeStmt(..) => todo!(),
                AstNode::ExternFn {
                    name,
                    ret_type,
                    args,
                    ..
                } => {
                    self.compile_extern_fn(name, ret_type, args)?;
                    (None, false)
                }
                AstNode::ReturnStmt(_l, v) => {
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
                AstNode::WhileStmt { cond, code, .. } => {
                    self.compile_while_expr(cond.as_ref(), code, func, trace)?;
                    (None, false)
                }
                AstNode::ForInStmt { var, of, block, .. } => {
                    self.compile_for_in_expr(var, of, block, func, trace)?;
                    (None, false)
                },
                AstNode::IfStmt { cond, block, .. } => (
                    None,
                    self.compile_if_stmt(cond.as_ref(), block, func, None, &[], trace)?,
                ),
                AstNode::DeferStmt(_l, code) => {
                    if let Some(scope) = self.deferred_items.last_mut() {
                        scope.insert(0, code.clone());
                    } else {
                        self.deferred_items.push(vec![code.clone()]);
                    }

                    (None, false)
                }
                AstNode::MatchExpr { matchee, arms, .. } => (self.compile_match(matchee, arms, func, trace)?, false),
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
                AstNode::BreakStmt(_l) => {
                    func.ins().jump(end_block, &*end_args.iter().map(|v| BlockArg::Value(*v)).collect::<Vec<_>>());

                    (None, true)
                }
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
            .push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
        sig.params.extend(
            arg_types
                .iter()
                .map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))),
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
            variants.push((ret_type.clone(), arg_types.iter().cloned().collect::<Vec<_>>()))
        } else {
            self.function_variants
                .insert(name.clone(), vec![(ret_type.clone(), arg_types.iter().cloned().collect::<Vec<_>>())]);
        }

        self.functions.insert(
            name.clone(),
            FunctionMeta {
                modifiers: vec![].into_boxed_slice(),
                arity: args.len(),
                arg_meta: arg_meta.into_iter().map(|(a, b)| (a.clone(), b)).collect::<Vec<_>>(),
                return_type: ret_type,
                sig,
                index: self.fn_counter,
                auto_free_idx: None,
                start_block: None,
            },
        );

        Ok(())
    }

    pub fn compile_array(&mut self, array: &[AstNode], func: &mut FunctionBuilder, trace: &Trace) -> Result<(StackSlot, Value, Type), Box<[CompilationError]>> {
        let mut values = vec![];

        for node in array {
            values.push(self.compile_body_expr(node, func, trace)?);
        }

        let (_, inner_type) = values.first().unwrap();

        let slot = func.create_sized_stack_slot(StackSlotData {
            key: None,
            kind: StackSlotKind::ExplicitSlot,
            size: (inner_type.size_bytes(&self.isa) as usize * array.len()) as u32,
            align_shift: 0,
        });

        for (index, node) in array.iter().enumerate() {
            let bytes = inner_type.size_bytes(&self.isa);

            let (value, _) = self.compile_body_expr(node, func, trace)?;

            func.ins().stack_store(value.clone(), slot, (index * bytes as usize) as i32);
        }

        Ok((slot, func.ins().stack_addr(self.isa.pointer_type(), slot, 0), Type::Slice(Box::new(values.first().unwrap().1.clone()), values.len() as u32, false, false)))
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
            Type::Slice(Indirection::new(Type::Int8), string.len() as u32, false, false),
        ))
    }

    pub fn estimate_type_of(&self, of: &AstNode) -> Option<Type> {
        match of {
            AstNode::NumberLiteral(_, n) => Some(Type::Int32),
            AstNode::StringLiteral(_, string) => Some(Type::Slice(Indirection::new(Type::Int8), string.len() as u32, false, false)),
            AstNode::BooleanLiteral(..) => Some(Type::Bool),
            AstNode::ByteLiteral(..) => Some(Type::UInt8),
            AstNode::DataInitExpr { name, .. } => Some(Type::DataPtr(self.data_declarations.get(name).map(|_| name.clone())?)),
            AstNode::NullLiteral(..) => Some(Type::Null),
            AstNode::Identifier(_, name) => self.var_builder.get_var_type(name),
            AstNode::CallExpr { callee, .. } => match callee.as_ref() {
                AstNode::Identifier(_, name) => self.functions.get(name).map(|m| m.return_type.clone()),
                AstNode::Path(_, p) => self.functions.get(&p[1]).map(|m| m.return_type.clone()),
                _ => None,
            },
            AstNode::GuardClause { cond, .. } => {
                let old_type = self.estimate_type_of(cond)?;

                if !old_type.is_pointer() {
                    return None;
                }

                match old_type {
                    Type::CPtr(i, m, _) => Some(Type::CPtr(i, m, false)),
                    Type::FatPtr(i, m, _) => Some(Type::FatPtr(i, m, false)),
                    Type::Slice(i, l, m, _) => Some(Type::Slice(i, l, m, false)),
                    _ => unreachable!()
                }
            }
            AstNode::ArrayLiteral(_, v) => Some(Type::Slice(Box::new(self.estimate_type_of(v.first()?)?), v.len() as u32, false, false)),
            AstNode::AsExpr(_l, val, ty) => {
                let vty = self.estimate_type_of(val.as_ref())?;
                let ty = self.tg.compile_type_no_tgs(ty, &self.isa);

                let (name, ty) = match ty {
                    Type::Declared(n, t) => (Some(n), t.deref().clone()),
                    t => (None, t),
                };

                let vty = match vty {
                    Type::Declared(_, t) => t.deref().clone(),
                    t => t,
                };

                if vty == ty {
                    return Some(ty)
                }

                let r = match (vty.clone(), ty.clone()) {
                    (Type::Int8, Type::Bool) | (Type::UInt8, Type::Bool) |(Type::Bool, Type::Int8) | (Type::Bool, Type::UInt8) => ty,
                    (Type::CPtr(i, ..), pty) if pty.is_pointer() && matches!(*i, Type::Any) => ty,
                    (Type::CPtr(_, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (Type::Slice(_, _, m1, n1), Type::Slice(_, _, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (Type::Slice(_, _, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (Type::FatPtr(_, m1, n1), Type::CPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (Type::CPtr(_, m1, n1), Type::FatPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (Type::Slice(inner, len, m1, n1), Type::FatPtr(_, m2, n2)) if (m1 == m2 || (m1 && !m2)) && n1 == n2 => ty,
                    (from, Type::Float32 | Type::Float64) if from.is_numeric() => ty,
                    (Type::DataPtr(..), Type::CPtr(inner, ..)) if matches!(inner.deref(), Type::Any) => ty,
                    (Type::Float32 | Type::Float64, to) if to.is_numeric() => ty,
                    (Type::Int64, p) | (p, Type::Int64) if p.is_pointer() => ty,
                    (from, to)
                        if (from.is_numeric() || matches!(from, Type::Bool)) && to.is_numeric() => to,
                    (from, to) => return None,
                };

                if let Some(name) = name {
                    Some(Type::Declared(name, Indirection::new(r)))
                } else {
                    Some(r)
                }
            },
            _ => None,
        }
    }

    fn get_calls_of_func(
        &mut self,
        name: &String,
    ) -> Result<Vec<Box<[Type]>>, Box<[CompilationError]>> {
        let usages = get_usages_of(name, &*self.nodes);
        let calls = usages[1..]
            .into_iter()
            .filter_map(|usage| match usage.kind {
                UsageKind::Call(ref args) => Some(args),
                _ => None,
            })
            .map(|args| args.iter().filter_map(|n| self.estimate_type_of(n)).collect::<Vec<_>>().into_boxed_slice())
            .collect::<Vec<_>>();

        Ok(calls)
    }

    pub fn compile_func(&mut self, node: &AstNode) -> Result<(), Box<[CompilationError]>> {
        let AstNode::FnStmt {
            of,
            name: unmangled_name,
            ret_type,
            args,
            type_generics,
            code,
            modifiers,
            ..
        } = node
        else {
            unreachable!();
        };

        /**** Search for calls of the function (if it has generics) ****/

        //if type_generics.len() > 0 {
        //    // Stores arguments found in calls of the generic function
        //    let mut usages = self.get_calls_of_func(unmangled_name)?;

        //    eprintln!("USAGES of {unmangled_name} -> {usages:#?}");
        //}

        let ret_type = self.tg.compile_type(&ret_type, &self.isa, type_generics);
        let arg_types = args
            .iter()
            .map(|(_, ty, _)| self.tg.compile_type(ty, &self.isa, type_generics))
            .collect::<Vec<_>>();

        let mangled_name = if modifiers.contains(&Modifier::NoMangle) || &**unmangled_name == "main" {
            unmangled_name.clone()
        } else if let Some(of) = of {
            mangle_method(of, unmangled_name, &arg_types, &ret_type)
        } else {
            mangle_function(unmangled_name, &arg_types, &ret_type)
        };

        println!("{unmangled_name} -> {mangled_name}");

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

        /*// main MUST have i32, *const i8 args
        if unmangled_name == "main" && arg_types != vec![CraneliftType::Int32, CraneliftType::CPtr(Indirection::new(CraneliftType::CPtr(Indirection::new(CraneliftType::Int8), false, false)), false, false)] {
            return Err(Box::new([CompilationError::MainMustHave2Args(self.file_path.clone())]))
        }*/

        let mut auto_free_idx = None;

        if modifiers.contains(&Modifier::AutoFree) {
            self.auto_frees.push(HashSet::new());
            auto_free_idx = Some(self.auto_frees.len() - 1);
        }

        let fid = self.module.declare_function(&*mangled_name, linkage, &sig).unwrap();

        self.fn_counter += 1;

        let mut func =
            Function::with_name_signature(UserFuncName::user(0, fid.index() as u32), sig.clone());

        self.fn_refs.insert(mangled_name.clone(), (func.clone(), fid));

        let mut ctx = FunctionBuilderContext::new();

        let mut fn_builder = FunctionBuilder::new(&mut func, &mut ctx);

        if modifiers.contains(&Modifier::Alloc) {
            self.allocator_fns.insert(mangled_name.clone());
        } else if modifiers.contains(&Modifier::Dealloc) {
            self.deallocator_fns.insert(mangled_name.clone());
        }

        let arg_meta = args
            .iter()
            .map(|(n, ty, _)| (n.clone(), self.tg.compile_type_no_tgs(ty, &self.isa)))
            .collect::<Vec<_>>();

        let block = fn_builder.create_block();

        fn_builder.append_block_params_for_function_params(block);

        fn_builder.switch_to_block(block);
        fn_builder.seal_block(block);

        if let Some(variants) = self.function_variants.get_mut(&mangled_name) {
            variants.push((ret_type.clone(), arg_types.clone()))
        } else {
            self.function_variants.insert(
                unmangled_name.clone(),
                vec![(ret_type.clone(), arg_types.clone())],
            );
        }

        self.functions.insert(
            mangled_name.clone(),
            FunctionMeta {
                auto_free_idx,
                modifiers: modifiers.clone(),
                arity: args.len(),
                arg_meta: arg_meta.into_iter().map(|(a, b)| (a.clone(), b)).collect::<Vec<_>>(),
                return_type: ret_type,
                sig,
                index: self.fn_counter,
                start_block: Some(block),
            },
        );

        let mut trace = Trace::new_root(mangled_name);

        self.var_builder.create_scope();

        for (i, (arg_name, arg_type, _)) in args.iter().enumerate() {
            let p = fn_builder.block_params(block)[i];
            let ty = self.tg.compile_type_no_tgs(arg_type, &self.isa);

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

        println!("{trace:?}");
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
                ..
            } => self.compile_extern_fn(name, ret_type, args),
            AstNode::DataStmt {
                name,
                fields,
                ..
            } => {
                let fields = fields.into_iter().map(|(m, n, t)| (m, n, self.tg.compile_type_no_tgs(t, &self.isa))).collect::<Vec<_>>();
                let (alignments, sizes): (Vec<u8>, Vec<u8>) = fields.iter().map(|(_, _, t)| (alignment_of_cranelift_type_on_architecture(t, self.isa.triple()).unwrap(), t.size_bytes(&self.isa))).unzip();

                let (data_size, data_offsets) = calculate_data_cranelift(&*alignments, &*sizes);

                let meta = DataDeclMeta {
                    size: data_size,
                    alignment: alignments.iter().max().unwrap_or(&1).clone(),
                    fields: fields.into_iter().map(|(m, n, t)| (m.clone(), n.clone(), t)).zip(data_offsets).map(|((a, b, c), d)| (d, a, b, c)).collect(),
                };

                self.data_declarations.insert(name.clone(), meta);

                Ok(())
            }
            AstNode::IncludeStmt(_l, p) => {
                let search_path = p.as_ref().split_last().unwrap().1.join("/");

                let mut msc_path: PathBuf = [search_path.clone(), format!("{}.msc", p.last().unwrap())].iter().collect();
                let mut obj_path: Option<PathBuf> = Some([search_path.clone(), format!("{}.o", p.last().unwrap())].iter().collect());

                // Attempt lookup in installed modules directory
                if !msc_path.exists() {
                    let home = homedir::my_home().unwrap().clone().unwrap();
                    let home = home.to_str();

                    if cfg!(target_os = "windows") {
                        msc_path = [home.unwrap(), "AppData", "Mosaic", "Modules", &*search_path, &*format!("{}.msc", p.last().unwrap())].iter().collect::<PathBuf>()
                    } else if cfg!(target_os = "macos") {
                       msc_path = [home.unwrap(), "Library", "Application Support", "Mosaic", "Modules", &*search_path, &*format!("{}.msc", p.last().unwrap())].iter().collect::<PathBuf>()
                    } else {
                        msc_path = [home.unwrap(), ".msc", "modules", &*search_path, &*format!("{}.msc", p.last().unwrap())].iter().collect::<PathBuf>()
                    };

                    let mut tmp = msc_path.clone();

                    tmp.set_extension("o");

                    obj_path = Some(tmp)
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

                let module_name = msc_path.file_stem().unwrap().to_str().unwrap().to_string();

                eprintln!("MODULE {module_name} IS MAYBE IN {:?}, CL {:?}", self.included_modules.iter().map(|m| m.name.clone()).collect::<Vec<_>>(), self.compiling_list);

                if self
                    .included_modules
                    .iter()
                    .any(|m| m.name == module_name)
                || self.compiling_list.contains(&module_name)
                {
                    return Ok(());
                }

                eprintln!("COMPILING MODULE {module_name} (NOT IN {:?} OR CL {:?})", self.included_modules.iter().map(|m| m.name.clone()).collect::<Vec<_>>(), self.compiling_list);

                let reader =
                    CharReader::new(File::new(msc_path.to_str().unwrap().to_string()).unwrap());

                let lexer = StreamedLexer::new(reader);
                let parser = StreamedParser::new(lexer);

                // Compile the module and add it to the included modules.

                let shadow_cg = Self::new(
                    parser,
                    isa::lookup(self.isa_builder.triple().clone()).unwrap(),
                    None,
                    Some(self.included_modules.clone()),
                    Some(self.compiling_list.clone())
                );

                let gen = shadow_cg.compile(true, obj_path.clone()).unwrap();

                eprintln!("previously included (from {}) -> {:?}", gen.name, gen.prev_includes.iter().map(|m| m.name.clone()).collect::<Vec<_>>());

                self.tg.merge(&*gen.tg);
                self.included_modules.extend(gen.prev_includes.clone());
                self.included_modules.insert(gen);

                eprintln!("MODULE {module_name} COMPILED (SHOULD BE IN {:?})", self.included_modules.iter().map(|m| m.name.clone()).collect::<Vec<_>>());

                Ok(())
            }
            AstNode::TypeAlias(_l, name, to) => {
                let to = self.tg.compile_type_no_tgs(to, &self.isa);

                self.tg.register_type(name, Type::Declared(name.clone(), Indirection::new(to)));

                Ok(())
            }
            n => unimplemented!("Global compilation of {n:?} (in {:?})", self.file_path),
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

        self.nodes = nodes.clone();

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

        if errors.len() > 0 {
            return Err(errors.into());
        }

        self.compiling_list.remove(&self.module_name);

        Ok(CraneliftModule {
            product: Rc::new(res),
            assoc_obj,
            name: self.module_name,
            prev_includes: self.included_modules,
            mosaic_file: self.file_path,
            functions: self.functions,
            data_declarations: self.data_declarations,
            function_variants: self.function_variants,
            tg: Rc::new(self.tg),
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
            func.ins().jump(end_block, &[BlockArg::Value(res)]);
        }

        /**** failure ****/

        func.switch_to_block(else_block);

        let ParseBlock::Plain(else_code) = else_code;
        let (Some((res, _)), _) = self.compile_body(else_code.as_ref(), func, trace)? else {
            func.switch_to_block(end_block);

            return Ok((None, filled));
        };

        func.ins().jump(end_block, &[BlockArg::Value(res)]);

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
                        func.ins().jump(end_block, &[BlockArg::Value(val)]);
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

                        func.ins().jump(end_block, &[BlockArg::Value(val)]);
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
