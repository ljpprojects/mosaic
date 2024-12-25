pub mod types;
pub mod module;
pub mod linker;
pub mod trace;
pub mod meta;
pub mod builders;

use crate::utils::IndirectionTrait;
use std::cmp::PartialEq;
use crate::compiler::cranelift::module::CraneliftModule;
use crate::compiler::cranelift::types::{CraneliftType as Type, CraneliftType, TypeGenerator};
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, Modifier, ParseBlock, ParseType, StreamedParser};
use crate::reader::CharReader;
use crate::utils::Indirection;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::{AbiParam, Function, GlobalValue, InstBuilder, MemFlags, Signature, UserFuncName, Value};
use cranelift_codegen::isa::{Builder, CallConv, OwnedTargetIsa, TargetFrontendConfig};
use cranelift_codegen::{ir, settings, Context};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{default_libcall_names, DataDescription, Linkage, Module};
use cranelift_native;
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;
use std::str::FromStr;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::immediates::Imm64;
use cranelift_codegen::settings::Configurable;
use crate::compiler::cranelift::builders::VariableBuilder;
use crate::compiler::cranelift::meta::FunctionMeta;
use crate::compiler::cranelift::trace::{ContextKind, Trace};
use crate::compiler::traits::CompilationType;
use crate::errors::CompilationError as CError;

type CompilationError = CError<CraneliftType>;

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
                        },
                        None => continue
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
    builder_ctx: FunctionBuilderContext,
    functions: HashMap<String, Vec<FunctionMeta>>,
    var_builder: VariableBuilder,
    module: ObjectModule,
    call_conv: CallConv,
    isa: OwnedTargetIsa,
    tg: TypeGenerator,
    included_modules: Vec<CraneliftModule>,
    /// Every value that should be auto-freed at the end of a scope,
    /// where auto_frees.last() = the current auto-free items.
    auto_frees: Vec<Vec<Value>>
}

impl CraneliftGenerator {
    pub fn new(parser: StreamedParser, isa_builder: Builder, module_name: String) -> Self {
        let file_path = parser.lexer.reader.reader.path().to_path_buf();

        let mut shared_builder = settings::builder();
        shared_builder.enable("is_pic").unwrap();
        shared_builder.set("opt_level", "speed_and_size").unwrap();

        let shared_flags = settings::Flags::new(shared_builder);

        shared_flags.enable_jump_tables();
        shared_flags.enable_pinned_reg();

        let isa = isa_builder.finish(shared_flags).unwrap();
        
        let call_conv = isa.default_call_conv();

        let obj_builder =
            ObjectBuilder::new(isa.clone(), module_name.clone(), default_libcall_names()).unwrap();

        let module = ObjectModule::new(obj_builder);

        Self {
            def_counter: 0,
            module_name,
            file_path,
            parser,
            builder_ctx: FunctionBuilderContext::new(),
            functions: Default::default(),
            var_builder: VariableBuilder::new(),
            module,
            call_conv,
            isa,
            fn_counter: 0,
            tg: TypeGenerator::new(),
            included_modules: vec![],
            auto_frees: vec![],
        }
    }

    pub fn compile_cmp_op(&mut self, op: &String, left: &AstNode, right: &AstNode, func: &mut FunctionBuilder, trace: &Trace) -> Result<(Value, Type), CompilationError> {
        match &**op {
            "==" => {
                let (left, lty) = self.compile_body_expr(left, func, trace)?;
                let (right, rty) = self.compile_body_expr(right, func, trace)?;
                
                if lty != rty {
                    return Ok((func.ins().iconst(ir::types::I8, 0), Type::Bool))
                }
                
                let ty_size = func.ins().iconst(ir::types::I64, lty.size_bytes(&self.isa) as i64);
                
                Ok((func.call_memcmp(self.isa.frontend_config(), left, right, ty_size), CraneliftType::Bool))
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
            op => return Err(CompilationError::UndefinedOperator(self.file_path.clone(), op.to_string()))
        }
    }

    pub fn compile_num_op(&mut self, op: &String, left: &AstNode, right: &AstNode, func: &mut FunctionBuilder, trace: &Trace) -> Result<(Value, Type), CompilationError> {
        match &**op {
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
            _ => self.compile_cmp_op(op, left, right, func, trace)
        }
    }

    pub fn compile_prefix_op(&mut self, op: &String, right: &AstNode, func: &mut FunctionBuilder, trace: &Trace) -> Result<(Value, Type), CompilationError> {
        match &**op {
            "&" => {
                let (right, ty) = self.compile_body_expr(right, func, trace)?;
                
                if matches!(ty, CraneliftType::Null) {
                    return Ok((func.ins().iconst(self.isa.pointer_type(), 0), CraneliftType::CPtr(Indirection::new(CraneliftType::Null))));
                }

                let mut sig = Signature::new(self.call_conv);

                sig.params.push(AbiParam::new(Type::Int32.into_cranelift(&self.isa)));
                sig.returns.push(AbiParam::new(self.isa.pointer_type()));

                let core_msc_alloc = self.module.declare_function("manmalloc", Linkage::Import, &sig).unwrap();
                let core_msc_alloc_fn = self.module.declare_func_in_func(core_msc_alloc, func.func);

                let size = func.ins().iconst(Type::Int32.into_cranelift(&self.isa), ty.size_bytes(&self.isa) as i64);

                let ptr = func.ins().call(core_msc_alloc_fn, &[size]);
                let ptr = func.inst_results(ptr)[0];

                func.ins().store(MemFlags::trusted().with_endianness(self.isa.endianness()), right, ptr, 0);

                Ok((ptr, Type::CPtr(Indirection::new(ty))))
            }
            _ => todo!("Handle error here")
        }
    }

    pub fn compile_body_expr(&mut self, expr: &AstNode, func: &mut FunctionBuilder, trace: &Trace) -> Result<(Value, Type), CompilationError> {
        match expr {
            AstNode::NumberLiteral(i) if i.fract() == 0f64 && trace.context == ContextKind::Idx => {
                Ok((func.ins().iconst(ir::types::I64, Imm64::new(*i as i64)), Type::Int64))
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
            AstNode::ByteLiteral(b) => Ok((func.ins().iconst(ir::types::I8, Imm64::new(*b as i64)), Type::Int8)),
            AstNode::StringLiteral(s) => self.compile_string(s, func),
            //AstNode::ArrayLiteral(a) => self.compile_array(a, func),
            AstNode::BooleanLiteral(b) if *b => Ok((func.ins().iconst(ir::types::I8, Imm64::new(1)), Type::Int8)),
            AstNode::BooleanLiteral(_) => Ok((func.ins().iconst(ir::types::I8, Imm64::new(0)), Type::Bool)),
            AstNode::NullLiteral => Ok((func.ins().iconst(ir::types::I8, Imm64::new(0)), Type::Null)),
            AstNode::Identifier(i) => Ok(self.var_builder.get_var(func, i).unwrap()),
            AstNode::InfixOp(l, o, r) => self.compile_num_op(o, l, r, func, &trace.nested_ctx(ContextKind::Normal)),
            AstNode::PrefixOp(op, r) => self.compile_prefix_op(op, r, func, &trace.nested_ctx(ContextKind::Normal)),
            AstNode::PostfixOp(_, _) => todo!(),
            AstNode::Path(_) => todo!(),
            AstNode::MemberExpr(_) => todo!(),
            AstNode::IdxAccess(of, idx) => {
                let (of, ty) = self.compile_body_expr(of, func, &trace.nested_ctx(ContextKind::Normal))?;
                let (idx, _) = self.compile_body_expr(idx, func, &mut trace.nested_ctx(ContextKind::Idx))?;

                println!("IDX {idx} OF {of}");

                let inner_ty = ty.inner().unwrap();
                let inner_ty_size = inner_ty.size_bytes(&self.isa) as i64;
                
                let offset = func.ins().imul_imm(idx, inner_ty_size);
                let computed_addr = func.ins().iadd(of, offset);

                Ok((func.ins().load(inner_ty.clone().into_cranelift(&self.isa), MemFlags::trusted().with_endianness(self.isa.endianness()), computed_addr, 0), inner_ty))
            },
            AstNode::CallExpr { callee, args } => {
                let AstNode::Identifier(name) = callee.as_ref() else {
                    todo!("Implement enums")
                };

                let mut value_args = vec![];
                
                for arg in args.iter() {
                    println!("ARG {arg}");
                    value_args.push(self.compile_body_expr(arg, func, &trace.nested_ctx(ContextKind::Normal))?.0);
                }

                let fn_meta = get_fn!(self, name).expect(&*format!("You sold: no function {name}")).first().unwrap();

                let fid = self.module.declare_function(name, Linkage::Import, &fn_meta.sig)
                    .unwrap();

                let local_func = self.module.declare_func_in_func(fid, func.func);
                
                let ret = func.ins().call(local_func, value_args.as_slice());
                let ret = func.inst_results(ret).first().map(|v| v.clone()).unwrap_or(func.ins().iconst(ir::types::I8, 0));

                if fn_meta.modifiers.contains(&Modifier::AutoFree) {
                    if self.auto_frees.len() == 0 {
                        self.auto_frees.push(vec![]);
                    }

                    self.auto_frees.last_mut().unwrap().push(ret.clone());
                }
                
                Ok((ret, fn_meta.return_type.clone()))
            },
            AstNode::AsExpr(val, ty) => {
                let (val, vty) = self.compile_body_expr(val, func, &trace.nested_ctx(ContextKind::Normal))?;
                let ty = self.tg.compile_type(ty, &self.isa);
                
                let (Type::CPtr(_), Type::CPtr(_)) = (vty, ty.clone()) else {
                    todo!()
                };

                Ok((val, ty))
            },
            AstNode::ForInExpr { .. } => todo!(),
            node => unimplemented!("Compile node {node}")
        }
    }

    pub fn compile_while_expr(&mut self, cond: &AstNode, code: &ParseBlock, func: &mut FunctionBuilder, trace: &Trace) -> Result<(), CompilationError> {
        let cond_block = func.create_block();
        let body_block = func.create_block();
        let end_block = func.create_block();

        func.ins().jump(cond_block, &[]);
        func.switch_to_block(cond_block);

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;
        func.ins().brif(cond, body_block, &[], end_block, &[]);

        func.switch_to_block(body_block);

        let ParseBlock::Plain(code) = code;
        self.compile_body(code.as_ref(), func, trace)?;
        func.ins().jump(cond_block, &[]);

        func.switch_to_block(end_block);

        func.seal_block(cond_block);
        func.seal_block(body_block);
        func.seal_block(end_block);

        Ok(())
    }
    
    pub fn compile_body(&mut self, body: &[AstNode], func: &mut FunctionBuilder, trace: &Trace) -> Result<Option<(Value, Type)>, CompilationError> {
        let mut r = None;

        for (i, stmt) in body.iter().enumerate() {
            if i == body.len() - 1 {

            }

            let res = match stmt {
                AstNode::DefStmt { name, def_type, value } => {
                    let ty = self.tg.compile_type(def_type, &self.isa);
                    let (val, _) = self.compile_body_expr(value, func, &trace.nested_ctx(ContextKind::Def(ty.clone())))?;

                    self.var_builder.create_var(func, val, (ty.clone(), ty.into_cranelift(&self.isa)), name.clone());

                    None
                }
                AstNode::ExternDef { name, def_type } => {
                    let ty = self.tg.compile_type(def_type, &self.isa);

                    self.var_builder.declare_var(func, (ty.clone(), ty.into_cranelift(&self.isa)), name.clone());

                    None
                }
                AstNode::IncludeStmt(_) => todo!(),
                AstNode::ExternFn { name, ret_type, args } => {
                    self.compile_extern_fn(name, ret_type, args)?;
                    None
                },
                AstNode::IfExpr { cond, block, else_clause } => self.compile_if_expr(cond.as_ref(), block, else_clause, func, trace)?,
                AstNode::ReturnStmt(v) => {
                    let (val, _) = self.compile_body_expr(v, func, trace)?;

                    let mut sig = Signature::new(self.call_conv);

                    sig.params.push(AbiParam::new(self.isa.pointer_type()));
                    sig.returns.push(AbiParam::new(Type::Null.into_cranelift(&self.isa)));

                    let core_msc_free = self.module.declare_function("core_msc_free", Linkage::Import, &sig).unwrap();
                    let core_msc_free_fn = self.module.declare_func_in_func(core_msc_free, func.func);

                    if let Some(popped) = self.auto_frees.pop() {
                        // free auto_frees
                        for auto_free in popped {
                            // call core_msc_free(auto_free)
                            println!("auto_free LEN {}: {}", trace.symbol, self.auto_frees.len());
                            func.ins().call(core_msc_free_fn, &[auto_free]);
                            println!("auto_free REM {auto_free} OF {}: {}", trace.symbol, self.auto_frees.len());
                        }
                    }

                    func.ins().return_(&[val]);
                    func.seal_all_blocks();

                    None
                }
                AstNode::WhileStmt { cond, code } => {
                    self.compile_while_expr(cond.as_ref(), code, func, trace)?;
                    None
                },
                AstNode::IfStmt { cond, block } => {
                    self.compile_if_stmt(cond.as_ref(), block, func, trace)?;
                    None
                },
                _ => Some(self.compile_body_expr(stmt, func, trace)?)
            };

            if i == body.len() - 1 {
                r = res
            }
        };
        
        Ok(r)
    }
    
    pub fn compile_extern_fn(&mut self, name: &String, ret_type: &ParseType, args: &Box<[(String, ParseType, Option<AstNode>)]>) -> Result<(), CompilationError> {
        let ret_type = self.tg.compile_type(&ret_type, &self.isa);
        let arg_types = args.iter().map(|(_, ty, _)| self.tg.compile_type(ty, &self.isa)).collect::<Vec<_>>();

        let mut sig = Signature::new(self.call_conv);

        sig.returns.push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
        sig.params.extend(arg_types.iter().map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))));

        self.module.declare_function(name, Linkage::Import, &sig)
            .unwrap();

        self.fn_counter += 1;

        let arg_meta = args.iter().map(|(n, ty, _)| {
            (n.clone(), self.tg.compile_type(ty, &self.isa))
        }).collect::<Vec<_>>();

        self.functions.insert(name.clone(), vec![FunctionMeta {
            modifiers: vec![].into_boxed_slice(),
            arity: args.len(),
            arg_meta,
            return_type: ret_type,
            sig,
            index: self.fn_counter,
            auto_free_idx: None,
            start_block: None
        }]);
        
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
    pub fn make_string(&mut self, string: &String, func: &mut FunctionBuilder) -> Result<GlobalValue, CompilationError> {
        let string_dat = self.module.declare_data(&*format!("str${}", self.def_counter), Linkage::Local, false, false).unwrap();

        self.def_counter += 1;

        let string = string.replace("\\n", "\n").replace("\\t", "\t");
        let string = string.replace("\\\"", "\"").replace("\\\\", "\\");
        let string = string.replace("\\0", "\0");

        let mut desc = DataDescription::new();
        desc.define([string.as_bytes(), &[0u8]].concat().to_vec().into_boxed_slice());
        
        self.module.define_data(string_dat, &desc).unwrap();

        Ok(self.module.declare_data_in_func(string_dat, func.func))
    }

    /// Returns a pointer to a string
    pub fn compile_string(&mut self, string: &String, func: &mut FunctionBuilder) -> Result<(Value, Type), CompilationError> {
        let global = self.make_string(string, func)?;
        
        Ok((func.ins().global_value(self.isa.pointer_type(), global), Type::Slice(Indirection::new(Type::Int8), string.len())))
    }
    
    pub fn compile_func(&mut self, node: &AstNode) -> Result<(), CompilationError> {
        let AstNode::FnExpr { name, ret_type, args, type_generics, code, modifiers } = node else {
            unreachable!();
        };

        let ret_type = self.tg.compile_type(&ret_type, &self.isa);
        let arg_types = args.iter().map(|(_, ty, _)| self.tg.compile_type(ty, &self.isa)).collect::<Vec<_>>();
        
        let mut sig = Signature::new(self.call_conv);
        
        sig.returns.push(AbiParam::new(ret_type.clone().into_cranelift(&self.isa)));
        sig.params.extend(arg_types.iter().map(|ty| AbiParam::new(ty.clone().into_cranelift(&self.isa))));
        
        let ParseBlock::Plain(code) = code;
        
        let linkage = if name == "main" || modifiers.contains(&Modifier::Export) {
            Linkage::Export
        } else {
            Linkage::Local
        };
        
        let fid = self.module
            .declare_function(&name, linkage, &sig)
            .unwrap();

        self.fn_counter += 1;
        
        let mut func = Function::with_name_signature(UserFuncName::user(0, fid.index() as u32), sig.clone());
        let mut func_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut func, &mut func_ctx);

        let mut auto_free_idx = None;

        if modifiers.contains(&Modifier::AutoFree) {
            self.auto_frees.push(vec![]);
            auto_free_idx = Some(self.auto_frees.len() - 1);
            println!("auto_free REG {name}: {}", self.auto_frees.len());
        }

        let arg_meta = args.iter().map(|(n, ty, _)| (n.clone(), self.tg.compile_type(ty, &self.isa))).collect::<Vec<_>>();

        let block = fn_builder.create_block();

        fn_builder.append_block_params_for_function_params(block);

        fn_builder.switch_to_block(block);
        fn_builder.seal_block(block);

        self.functions.insert(name.clone(), vec![FunctionMeta {
            modifiers: modifiers.clone(),
            arity: args.len(),
            arg_meta,
            return_type: ret_type,
            sig,
            index: self.fn_counter,
            auto_free_idx,
            start_block: Some(block)
        }]);

        let mut trace = Trace::new_root(name.clone());
        
        for (i, (arg_name, arg_type, _)) in args.iter().enumerate() {
            if let None = self.var_builder.get_var(&mut fn_builder, arg_name) {
                let p = fn_builder.block_params(block)[i];
                let ty = self.tg.compile_type(arg_type, &self.isa);
                self.var_builder.create_var(&mut fn_builder, p, (ty.clone(), ty.into_cranelift(&self.isa)), arg_name.clone());
            }
        }
        
        self.compile_body(code.as_ref(), &mut fn_builder, &mut trace)?;

        fn_builder.finalize();

        let mut context = Context::for_function(func.clone());

        self.module.define_function(fid, &mut context).unwrap();

        context.eliminate_unreachable_code(self.isa.as_ref()).unwrap();
        context.optimize(self.isa.as_ref(), &mut ControlPlane::default()).unwrap();
        context.replace_redundant_loads().unwrap();
        
        Ok(())
    }
    
    pub fn compile_global(&mut self, node: &AstNode) -> Result<(), CompilationError> {
        match node {
            AstNode::FnExpr { .. } => self.compile_func(node),
            AstNode::ExternFn { name, ret_type, args } => self.compile_extern_fn(name, ret_type, args),
            AstNode::IncludeStmt(p) => {
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

                // Compile the module and add it to the included modules.

                let shadow_cg = Self::new(parser, cranelift_native::builder().unwrap(), msc_path.file_stem().unwrap().to_str().unwrap().to_string());
                
                let gen = shadow_cg.compile(true, obj_path.clone())?;

                self.tg.merge(&gen.tg);
                self.included_modules.push(gen);

                fs::File::open(msc_path.clone()).map_err(|_| format!("{}::{}", search_path.replace("/", "::"), p.last().unwrap())).unwrap();
                
                Ok(())
            }
            n => unimplemented!("Global compilation of {n:?}")
        }
    }
    
    pub fn compile(mut self, write: bool, assoc_obj: Option<PathBuf>) -> Result<CraneliftModule, CompilationError> {
        for node in self.parser.iter() {
            self.compile_global(&node.unwrap())?;
        }

        let res = self.module.finish();

        let mut out_file = self.file_path.clone();

        out_file.set_file_name(format!("{M}.cmp.o", M = self.module_name));

        if write {
            let mut file = fs::File::create(out_file.clone()).unwrap();
            res.object.write_stream(&mut file).unwrap();
        }

        let prev_includes = self.included_modules.iter().map(|m| [m.prev_includes.clone().into_iter().collect(), vec![(m.mosaic_file.clone(), m.assoc_obj.clone())]].into_iter().flatten()).flatten().collect::<Vec<_>>();


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

    fn compile_if_expr(&mut self, cond: &AstNode, code: &ParseBlock, else_code: &ParseBlock, func: &mut FunctionBuilder, trace: &Trace) -> Result<Option<(Value, CraneliftType)>, CompilationError> {
        let success_block = func.create_block();
        let else_block = func.create_block();
        let end_block = func.create_block();

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;

        func.ins().brif(cond, success_block, &[], else_block, &[]);

        /**** success ****/

        func.switch_to_block(success_block);

        let ParseBlock::Plain(code) = code;

        // TODO: If statements with else clauses
        let Some((res, res_ty)) = self.compile_body(code.as_ref(), func, trace)? else {
            func.ins().jump(end_block, &[]);

            /**** failure ****/

            func.switch_to_block(else_block);

            let ParseBlock::Plain(else_code) = else_code;
            self.compile_body(else_code.as_ref(), func, trace)?;

            func.ins().jump(end_block, &[]);

            func.switch_to_block(end_block);

            func.seal_block(success_block);
            func.seal_block(else_block);
            func.seal_block(end_block);

            return Ok(None)
        };
        
        func.append_block_param(end_block, res_ty.clone().into_cranelift(&self.isa));

        func.ins().jump(end_block, &[res]);

        /**** failure ****/

        func.switch_to_block(else_block);

        let ParseBlock::Plain(else_code) = else_code;
        let (res, _) = self.compile_body(else_code.as_ref(), func, trace)?.unwrap();

        func.ins().jump(end_block, &[res]);

        func.switch_to_block(end_block);

        func.seal_block(success_block);
        func.seal_block(else_block);
        func.seal_block(end_block);

        let result = func.block_params(end_block)[0];

        Ok(Some((result, res_ty)))
    }

    // TODO: If statements \w else clauses
    fn compile_if_stmt(&mut self, cond: &AstNode, code: &ParseBlock, func: &mut FunctionBuilder, trace: &Trace) -> Result<(), CompilationError> {
        let success_block = func.create_block();
        let else_block = func.create_block();
        let end_block = func.create_block();

        let (cond, _) = self.compile_body_expr(cond, func, trace)?;

        func.ins().brif(cond, success_block, &[], else_block, &[]);

        /**** success ****/

        func.switch_to_block(success_block);

        let ParseBlock::Plain(code) = code;

        // TODO: If statements with else clauses
        self.compile_body(code.as_ref(), func, trace)?;
        func.ins().jump(end_block, &[]);
        func.switch_to_block(end_block);

        func.seal_block(success_block);
        func.seal_block(else_block);
        func.seal_block(end_block);

        Ok(())
    }
}