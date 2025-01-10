pub mod builders;
pub mod linker;
pub mod meta;
pub mod module;
pub mod trace;
pub mod types;
pub mod value;

use crate::cli::Command;
use crate::compiler::analyser::PreoptEngine;
use crate::compiler::cranelift::builders::VariableBuilder;
use crate::compiler::cranelift::meta::{FunctionMeta, MustFreeMeta, StructMeta};
use crate::compiler::cranelift::module::CraneliftModule;
use crate::compiler::cranelift::trace::{ContextKind, Trace};
use crate::compiler::cranelift::types::{CraneliftType as Type, CraneliftType, TypeGenerator};
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, Modifier, ParseBlock, ParseType, StreamedParser};
use crate::reader::CharReader;
use crate::utils::Indirection;
use colored::Colorize;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::immediates::Imm64;
use cranelift_codegen::ir::{
    AbiParam, Block, ConstantData, Function, GlobalValue, InstBuilder, MemFlags, Signature,
    UserFuncName, Value,
};
use cranelift_codegen::isa::{Builder, CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::Configurable;
use cranelift_codegen::{ir, isa, settings, Context};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{default_libcall_names, DataDescription, Linkage, Module};
use cranelift_native;
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;

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

pub struct CraneliftGenerator {
    def_counter: usize,
    module_name: String,
    fn_counter: u32,
    file_path: PathBuf,
    parser: StreamedParser,
    builder_ctx: RefCell<FunctionBuilderContext>,
    functions: HashMap<String, Vec<FunctionMeta>>,
    structs: HashMap<String, StructMeta>,
    var_builder: VariableBuilder,
    module: ObjectModule,
    call_conv: CallConv,
    isa: OwnedTargetIsa,
    isa_builder: Builder,
    tg: TypeGenerator,
    included_modules: Vec<CraneliftModule>,
    /// Every value that should be auto-freed at the end of a scope,
    /// where auto_frees.last() = the current auto-free items.
    auto_frees: Vec<HashSet<Value>>,

    allocator_fns: HashSet<String>,
    deallocator_fns: HashSet<String>,
    must_frees: HashSet<MustFreeMeta>,
    command: Option<Command>,
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
        let _ = shared_builder.enable("sign_return_address");

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
            def_counter: 0,
            module_name,
            file_path,
            parser,
            builder_ctx: RefCell::new(FunctionBuilderContext::new()),
            functions: Default::default(),
            structs: Default::default(),
            var_builder: VariableBuilder::new(&isa),
            module,
            call_conv,
            isa,
            fn_counter: 0,
            isa_builder,
            tg: TypeGenerator::new(),
            included_modules: vec![],
            auto_frees: vec![],
            allocator_fns: HashSet::new(),
            deallocator_fns: HashSet::new(),
            must_frees: HashSet::new(),
            command,
        }
    }

    pub fn compile_struct(
        &mut self,
        name: &String,
        fields: HashMap<String, (Box<[Modifier]>, ParseType, Option<AstNode>)>,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(), CompilationError> {
        let fields = fields
            .into_iter()
            .map(|(k, (m, t, d))| (k, (m, self.tg.compile_type(&t, &self.isa), d)))
            .collect::<HashMap<_, _>>();

        Ok(())
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
            op => {
                return Err(Box::new([CompilationError::UndefinedOperator(
                    self.file_path.clone(),
                    op.to_string(),
                )]))
            }
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
            "=" => {
                let AstNode::Identifier(name) = left else {
                    if let AstNode::IdxAccess(of, idx) = left {
                        let (right, rty) = self.compile_body_expr(right, func, trace)?;

                        let (of, ty) = self.compile_body_expr(
                            of,
                            func,
                            &trace.nested_ctx(ContextKind::Normal),
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
                    } else {
                        todo!()
                    }
                };

                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                self.var_builder
                    .set_var(func, name, &right, &rty, self.file_path.clone())?;

                Ok((right, rty))
            }
            "+" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fadd(left, right), Type::Float64)
                } else {
                    (func.ins().iadd(left, right), Type::Int64)
                };

                Ok((res, ty))
            }
            "-" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fsub(left, right), Type::Float64)
                } else {
                    (func.ins().isub(left, right), Type::Int64)
                };

                Ok((res, ty))
            }
            "*" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, _rty) = self.compile_body_expr(right, func, trace)?;

                let (res, ty) = if matches!(lty, Type::Float32) || matches!(lty, Type::Float64) {
                    (func.ins().fmul(left, right), Type::Float64)
                } else {
                    (func.ins().imul(left, right), Type::Int64)
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
            "!" => {
                let (right, rty) = self.compile_body_expr(right, func, trace)?;

                assert!(matches!(rty, Type::Bool));

                Ok((func.ins().bxor_imm(right, 1), Type::Bool))
            }
            "&" => {
                if let AstNode::Identifier(name) = right {
                    let (ptr, ty) =
                        self.var_builder
                            .get_var_ptr(func, name, self.file_path.clone())?;

                    return Ok((ptr, Type::CPtr(Indirection::new(ty))));
                }

                let (right, ty) = self.compile_body_expr(right, func, trace)?;

                if matches!(ty, CraneliftType::Null) {
                    return Ok((
                        func.ins().iconst(self.isa.pointer_type(), 0),
                        CraneliftType::CPtr(Indirection::new(CraneliftType::Null)),
                    ));
                }

                let mut sig = Signature::new(self.call_conv);

                sig.params
                    .push(AbiParam::new(Type::Int32.into_cranelift(&self.isa)));
                sig.returns.push(AbiParam::new(self.isa.pointer_type()));

                let core_msc_alloc = self
                    .module
                    .declare_function("malloc", Linkage::Import, &sig)
                    .unwrap();
                let core_msc_alloc_fn = self.module.declare_func_in_func(core_msc_alloc, func.func);

                let size = func.ins().iconst(
                    Type::Int32.into_cranelift(&self.isa),
                    ty.size_bytes(&self.isa) as i64,
                );

                let ptr = func.ins().call(core_msc_alloc_fn, &[size]);
                let ptr = func.inst_results(ptr)[0];

                // Make sure the allocated pointer is freed
                if let Some(scope) = self.auto_frees.last_mut() {
                    scope.insert(ptr.clone());
                } else {
                    self.auto_frees.push([ptr.clone()].into());
                }

                func.ins().store(
                    MemFlags::trusted().with_endianness(self.isa.endianness()),
                    right,
                    ptr,
                    0,
                );

                Ok((ptr, Type::CPtr(Indirection::new(ty))))
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
            AstNode::NumberLiteral(i) if i.fract() == 0f64 && trace.context == ContextKind::Idx => {
                Ok((
                    func.ins().iconst(ir::types::I64, Imm64::new(*i as i64)),
                    Type::Int64,
                ))
            }
            AstNode::NumberLiteral(i) if i.fract() == 0f64 => {
                let ty = if let ContextKind::Def(ty) = &trace.context {
                    ty.clone()
                } else {
                    Type::Int32
                };

                Ok((func.ins().iconst(ir::types::I32, Imm64::new(*i as i64)), ty))
            }
            AstNode::NumberLiteral(i) => Ok((func.ins().f64const(*i), Type::Float64)),
            AstNode::ByteLiteral(b) => Ok((
                func.ins().iconst(ir::types::I8, Imm64::new(*b as i64)),
                Type::Int8,
            )),
            AstNode::StringLiteral(s) => self.compile_string(s, func),
            //AstNode::ArrayLiteral(a) => self.compile_array(a, func),
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
                Ok(self.var_builder.get_var(func, i, self.file_path.clone())?)
            }
            AstNode::InfixOp(l, o, r) => {
                self.compile_num_op(o, l, r, func, &trace.nested_ctx(ContextKind::Normal))
            }
            AstNode::PrefixOp(op, r) => {
                self.compile_prefix_op(op, r, func, &trace.nested_ctx(ContextKind::Normal))
            }
            AstNode::PostfixOp(_, _) => todo!(),
            AstNode::Path(_) => todo!(),
            AstNode::MemberExpr(_) => todo!(),
            AstNode::IdxAccess(of, idx) => {
                let (of, ty) =
                    self.compile_body_expr(of, func, &trace.nested_ctx(ContextKind::Normal))?;
                let (idx, _) =
                    self.compile_body_expr(idx, func, &mut trace.nested_ctx(ContextKind::Idx))?;

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
            AstNode::CallExpr { callee, args } => {
                let AstNode::Identifier(name) = callee.as_ref() else {
                    todo!("Implement enums")
                };

                let mut value_args = vec![];

                for arg in args.iter() {
                    value_args.push(
                        self.compile_body_expr(arg, func, &trace.nested_ctx(ContextKind::Normal))?
                            .0,
                    );
                }

                let fn_meta = get_fn!(self, name)
                    .map(|s| Ok(s))
                    .unwrap_or(Err(Box::from(
                        [CompilationError::UndefinedFunction(
                            self.file_path.clone(),
                            name.clone(),
                        )]
                        .as_slice(),
                    )))?
                    .first()
                    .unwrap();

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

                Ok((ret, fn_meta.return_type.clone()))
            }
            AstNode::AsExpr(val, ty) => {
                let (val, vty) =
                    self.compile_body_expr(val, func, &trace.nested_ctx(ContextKind::Normal))?;
                let ty = self.tg.compile_type(ty, &self.isa);

                match (vty.clone(), ty.clone()) {
                    (Type::CPtr(_), Type::CPtr(_)) => Ok((val, ty)),
                    (Type::Slice(..), Type::Slice(..)) => Ok((val, ty)),
                    (Type::Slice(..), Type::CPtr(..)) => Ok((val, ty)),
                    (Type::Slice(inner, _), Type::CStr)
                        if matches!(inner.deref(), Type::Int8 | Type::UInt8) =>
                    {
                        Ok((val, ty))
                    }
                    (Type::CPtr(inner), Type::CStr)
                        if matches!(inner.deref(), Type::Int8 | Type::UInt8 | Type::Any) =>
                    {
                        Ok((val, ty))
                    }
                    (from, to) if from.is_numeric() && to.is_numeric() => {
                        let casted = if from.size_bytes(&self.isa) > to.size_bytes(&self.isa) {
                            func.ins()
                                .ireduce(to.clone().into_cranelift(&self.isa), val)
                        } else {
                            func.ins()
                                .sextend(to.clone().into_cranelift(&self.isa), val)
                        };

                        Ok((casted, to))
                    }
                    (from, to) => Err(Box::new([CompilationError::InvalidCast(
                        self.file_path.clone(),
                        from,
                        to,
                    )])),
                }
            }
            AstNode::ForInExpr { .. } => todo!(),
            node => unimplemented!("Compile node {node}"),
        }
    }

    pub fn compile_while_expr(
        &mut self,
        cond: &AstNode,
        code: &ParseBlock,
        func: &mut FunctionBuilder,
        trace: &Trace,
    ) -> Result<(), Box<[CompilationError]>> {
        let cond_block = func.create_block();
        let body_block = func.create_block();
        let end_block = func.create_block();

        func.ins().jump(cond_block, &[]);
        func.switch_to_block(cond_block);

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;
        func.ins().brif(cond, body_block, &[], end_block, &[]);

        func.switch_to_block(body_block);

        let ParseBlock::Plain(code) = code;
        let (_, filled) =
            self.compile_while_body(code.as_ref(), func, trace, end_block.clone(), &[])?;

        if !filled {
            func.ins().jump(cond_block, &[]);
        }

        func.switch_to_block(end_block);

        func.seal_block(cond_block);
        func.seal_block(body_block);
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

        for (i, stmt) in body.iter().enumerate() {
            let res = match stmt {
                AstNode::LetStmt {
                    name,
                    def_type,
                    value,
                } => {
                    let ty = self.tg.compile_type(def_type, &self.isa);
                    let (val, _) = self.compile_body_expr(
                        value,
                        func,
                        &trace.nested_ctx(ContextKind::Def(ty.clone())),
                    )?;

                    let mut sig = Signature::new(self.call_conv);
                    sig.params
                        .push(AbiParam::new(Type::Int32.into_cranelift(&self.isa)));
                    sig.returns.push(AbiParam::new(self.isa.pointer_type()));

                    let core_msc_alloc = self
                        .module
                        .declare_function("malloc", Linkage::Import, &sig)
                        .unwrap();
                    let core_msc_alloc_fn =
                        self.module.declare_func_in_func(core_msc_alloc, func.func);

                    self.var_builder.create_var(
                        func,
                        val,
                        ty.clone(),
                        name.clone(),
                        true,
                        core_msc_alloc_fn,
                    );

                    (None, false)
                }
                AstNode::MutStmt {
                    name,
                    def_type,
                    value,
                } => {
                    let ty = self.tg.compile_type(def_type, &self.isa);
                    let (val, _) = self.compile_body_expr(
                        value,
                        func,
                        &trace.nested_ctx(ContextKind::Def(ty.clone())),
                    )?;

                    let mut sig = Signature::new(self.call_conv);
                    sig.params
                        .push(AbiParam::new(Type::Int32.into_cranelift(&self.isa)));
                    sig.returns.push(AbiParam::new(self.isa.pointer_type()));

                    let core_msc_alloc = self
                        .module
                        .declare_function("malloc", Linkage::Import, &sig)
                        .unwrap();
                    let core_msc_alloc_fn =
                        self.module.declare_func_in_func(core_msc_alloc, func.func);

                    self.var_builder.create_var(
                        func,
                        val,
                        ty.clone(),
                        name.clone(),
                        false,
                        core_msc_alloc_fn,
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
                AstNode::IfExpr {
                    cond,
                    block,
                    else_clause,
                } => self.compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?,
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

                    func.ins().return_(&[val]);
                    func.seal_all_blocks();

                    (None, true)
                }
                AstNode::WhileStmt { cond, code } => {
                    self.compile_while_expr(cond.as_ref(), code, func, trace)?;
                    (None, false)
                }
                AstNode::IfStmt { cond, block } => (
                    None,
                    self.compile_if_stmt(cond.as_ref(), block, func, None, &[], trace)?,
                ),
                _ => (Some(self.compile_body_expr(stmt, func, trace)?), false),
            };

            if i == body.len() - 1 {
                r = res
            }
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
        let ret_type = self.tg.compile_type(&ret_type, &self.isa);
        let arg_types = args
            .iter()
            .map(|(_, ty, _)| self.tg.compile_type(ty, &self.isa))
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
            .map(|(n, ty, _)| (n.clone(), self.tg.compile_type(ty, &self.isa)))
            .collect::<Vec<_>>();

        self.functions.insert(
            name.clone(),
            vec![FunctionMeta {
                modifiers: vec![].into_boxed_slice(),
                arity: args.len(),
                arg_meta,
                return_type: ret_type,
                sig,
                index: self.fn_counter,
                auto_free_idx: None,
                start_block: None,
            }],
        );

        Ok(())
    }

    /*pub fn compile_array(&mut self, array: &[AstNode], func: &mut FunctionBuilder) -> StackSlot {
        let mut values = vec![];

        for node in array {
            values.push(self.compile_body_expr(node, func));
        }

        let inner_type = values.first().unwrap();

        let slot = func.create_sized_stack_slot(StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: inner_type.bytes() * array.len() as u32,
            align_shift: 8,
        });

        for (index, node) in values.iter().enumerate() {
            let bytes = inner_type.bytes();

            let value = self.compile_body_expr(node, func);

            func.ins().stack_store(value.clone(), slot, (index * bytes as usize) as i32);
        }

        slot
    }*/

    /// Returns a global value containing the string
    pub fn make_string(
        &mut self,
        string: &String,
        func: &mut FunctionBuilder,
    ) -> Result<GlobalValue, Box<[CompilationError]>> {
        let string_dat = self
            .module
            .declare_data(
                &*format!("str${}", self.def_counter),
                Linkage::Local,
                false,
                false,
            )
            .unwrap();

        self.def_counter += 1;

        let string = string.replace("\\\"", "\"").replace("\\\\", "\\");
        let string = string.replace("\\0", "\0");
        let string = string.replace("\\red", &*"".red().to_string());
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
            Type::Slice(Indirection::new(Type::Int8), string.len()),
        ))
    }

    pub fn compile_func(&mut self, node: &AstNode) -> Result<(), Box<[CompilationError]>> {
        let AstNode::FnExpr {
            name,
            ret_type,
            args,
            type_generics: _,
            code,
            modifiers,
        } = node
        else {
            unreachable!();
        };

        let ret_type = self.tg.compile_type(&ret_type, &self.isa);
        let arg_types = args
            .iter()
            .map(|(_, ty, _)| self.tg.compile_type(ty, &self.isa))
            .collect::<Vec<_>>();

        let mut sig = Signature::new(self.call_conv);

        sig.returns
            .push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
        sig.params.extend(
            arg_types
                .iter()
                .map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))),
        );

        let ParseBlock::Plain(code) = code;

        let linkage = if name == "main" || modifiers.contains(&Modifier::Export) {
            Linkage::Export
        } else {
            Linkage::Local
        };

        let fid = self.module.declare_function(&name, linkage, &sig).unwrap();

        self.fn_counter += 1;

        let mut func =
            Function::with_name_signature(UserFuncName::user(0, fid.index() as u32), sig.clone());

        let mut ctx = FunctionBuilderContext::new();

        let mut fn_builder = FunctionBuilder::new(&mut func, &mut ctx);

        let mut auto_free_idx = None;

        if modifiers.contains(&Modifier::AutoFree) {
            self.auto_frees.push(HashSet::new());
            auto_free_idx = Some(self.auto_frees.len() - 1);
        }

        if modifiers.contains(&Modifier::Alloc) {
            self.allocator_fns.insert(name.clone());
        } else if modifiers.contains(&Modifier::Dealloc) {
            self.deallocator_fns.insert(name.clone());
        }

        let arg_meta = args
            .iter()
            .map(|(n, ty, _)| (n.clone(), self.tg.compile_type(ty, &self.isa)))
            .collect::<Vec<_>>();

        let block = fn_builder.create_block();

        fn_builder.append_block_params_for_function_params(block);

        fn_builder.switch_to_block(block);
        fn_builder.seal_block(block);

        let fpty = Type::FuncPtr {
            ret_type: Indirection::new(ret_type.clone()),
            arg_types: arg_types
                .iter()
                .map(|a| Indirection::new(a.clone()))
                .collect(),
        };

        let fptr = self.module.declare_func_in_func(fid, fn_builder.func);
        let fptr = fn_builder
            .ins()
            .func_addr(fpty.clone().into_cranelift(&self.isa), fptr);

        let mut alloc_sig = Signature::new(self.isa.default_call_conv());

        alloc_sig.params.push(AbiParam::new(
            CraneliftType::Int32.into_cranelift(&self.isa),
        ));
        alloc_sig
            .returns
            .push(AbiParam::new(self.isa.pointer_type()));

        let alloc_fn = self
            .module
            .declare_function("malloc", Linkage::Import, &alloc_sig)
            .unwrap();
        let alloc_fn = self.module.declare_func_in_func(alloc_fn, fn_builder.func);

        self.var_builder
            .create_var(&mut fn_builder, fptr, fpty, name.clone(), true, alloc_fn);

        self.functions.insert(
            name.clone(),
            vec![FunctionMeta {
                auto_free_idx,
                modifiers: modifiers.clone(),
                arity: args.len(),
                arg_meta,
                return_type: ret_type,
                sig,
                index: self.fn_counter,
                start_block: Some(block),
            }],
        );

        let mut trace = Trace::new_root(name.clone());

        self.var_builder.create_scope();

        for (i, (arg_name, arg_type, _)) in args.iter().enumerate() {
            let p = fn_builder.block_params(block)[i];
            let ty = self.tg.compile_type(arg_type, &self.isa);

            let mut sig = Signature::new(self.call_conv);
            sig.params
                .push(AbiParam::new(Type::Int32.into_cranelift(&self.isa)));
            sig.returns.push(AbiParam::new(self.isa.pointer_type()));

            let core_msc_alloc = self
                .module
                .declare_function("malloc", Linkage::Import, &sig)
                .unwrap();
            let core_msc_alloc_fn = self
                .module
                .declare_func_in_func(core_msc_alloc, fn_builder.func);

            self.var_builder.create_var(
                &mut fn_builder,
                p,
                ty,
                arg_name.clone(),
                true,
                core_msc_alloc_fn,
            );
        }

        self.compile_body(code.as_ref(), &mut fn_builder, &mut trace)?;

        fn_builder.finalize();

        let mut context = Context::for_function(func.clone());

        if &**name == "main" {
            if self.must_frees.len() != 0 {
                let mut errors = vec![];

                for item in self.must_frees.iter() {
                    errors.push(CompilationError::NotFreed(
                        self.file_path.clone(),
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
            AstNode::FnExpr { .. } => self.compile_func(node),
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

                let mut msc_path = PathBuf::from(format!(
                    "{parent_path}/{search_path}/{}.msc",
                    p.last().unwrap()
                ));
                let mut obj_path: Option<_> = Some(PathBuf::from(format!(
                    "{parent_path}/{search_path}/{}.o",
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

                if let Some(ref p) = obj_path
                    && !p.exists()
                {
                    obj_path = None;
                }

                if !msc_path.exists() {
                    println!("MODULE NOT FOUND AT {msc_path:?}");

                    return Err(Box::new([CompilationError::UnknownModule(
                        self.file_path.clone(),
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

        let mut engine = PreoptEngine::new(&*nodes);

        engine.removed_unused_defs();
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
            .map(|m| {
                [
                    m.prev_includes.clone().into_iter().collect(),
                    vec![(m.mosaic_file.clone(), m.assoc_obj.clone())],
                ]
                .into_iter()
                .flatten()
            })
            .flatten()
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

        func.ins().jump(end_block, &[res]);

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
