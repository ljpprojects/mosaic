pub mod errors;
pub mod linker;
pub mod types;

use crate::compiler::errors::{GenerationError, GenerationResult};
use crate::compiler::linker::MosaicModule;
use crate::compiler::types::TypeGenerator;
use crate::compiler::types::{Type, CSTRING_TYPES};
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, ParseBlock, ParseType, StreamedParser};
use crate::reader::CharReader;
use crate::utils::Indirection;
use qbe::{Cmp, DataDef, DataItem, Function, Instr, Linkage, Module, TypeDef, Value};
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fs;
use std::hash::Hash;
use std::ops::Deref;
use std::path::PathBuf;
use std::str::FromStr;

type ArgMeta = (String, Type, Option<Value>);
type ValuePair = (Type, Value);
type FunctionMeta = (Type, Box<[ArgMeta]>);

#[derive(Debug, Clone)]
/// Generates code from many [AstNodes](AstNode)
pub struct CodeGen<'a> {
    /// A counter to provide unique names
    unique_name_counter: u32,
    module: Module<'a>,
    types: HashMap<String, Type>,
    scopes: Vec<HashMap<String, ValuePair>>,
    functions: HashMap<String, FunctionMeta>,
    datadefs: Vec<DataDef<'a>>,
    code: Box<[AstNode]>,
    used_modules: Vec<MosaicModule>,
    typedefs: Vec<TypeDef<'a>>,
}

impl<'a> CodeGen<'a> {
    fn generate_temp(&mut self) -> Value {
        self.unique_name_counter += 1;
        Value::Temporary(format!("tmp.{}", self.unique_name_counter))
    }

    fn get_var(&self, name: String) -> GenerationResult<&ValuePair> {
        self.scopes
            .iter()
            .rev()
            .filter_map(|s| s.get(&name))
            .next()
            .ok_or_else(|| GenerationError::UndefinedSymbol(name))
    }

    fn declare_var(&mut self, r#type: Type, name: String) -> GenerationResult<Value> {
        if self.get_var(name.clone()).is_ok() {
            return Err(GenerationError::DoubleDefinition(name));
        }

        let tmp = self.generate_temp();

        let scope = self
            .scopes
            .last_mut()
            .expect("expected last scope to be present");
        scope.insert(name.to_owned(), (r#type, tmp.to_owned()));

        Ok(tmp)
    }

    fn generate_string(&mut self, string: String) -> GenerationResult<ValuePair> {
        self.unique_name_counter += 1;

        let name = format!("string.{}", self.unique_name_counter);

        let mut items: Vec<(qbe::Type, qbe::DataItem)> = Vec::new();
        let mut buf = String::new();
        for ch in string.chars() {
            if ch.is_ascii() && !ch.is_ascii_control() && ch != '"' {
                buf.push(ch)
            } else {
                if !buf.is_empty() {
                    items.push((qbe::Type::Byte, qbe::DataItem::Str(buf.clone())));
                    buf.clear();
                }

                let mut buf = [0; 4];
                let len = ch.encode_utf8(&mut buf).len();

                for b in buf.iter().take(len) {
                    items.push((qbe::Type::Byte, qbe::DataItem::Const(*b as u64)));
                }

                continue;
            }
        }

        if !buf.is_empty() {
            items.push((qbe::Type::Byte, qbe::DataItem::Str(buf)));
        }

        let len = items.len() as u32;

        self.datadefs.push(DataDef {
            linkage: qbe::Linkage::private(),
            name: name.clone(),
            align: None,
            items,
        });

        Ok((
            Type::FatPointer(Indirection::new(Type::Integer8), len),
            Value::Global(name),
        ))
    }

    fn generate_array(
        &mut self,
        func: &mut Function<'a>,
        len: u32,
        items: Box<[AstNode]>,
    ) -> GenerationResult<ValuePair> {
        let mut first_type: Option<Type> = None;
        let mut results: Vec<Value> = Vec::new();

        for item in items.iter() {
            let (ty, result) = self.generate_expr(item.clone(), func)?;
            
            results.push(result);

            if let Some(first_type) = first_type.clone() {
                if ty != first_type {
                    return Err(GenerationError::MismatchedType("array".into(), first_type, ty));
                }
            } else {
                first_type = Some(ty);
            }
        }

        // Arrays have the following in-memory representation:
        // {
        //    length (word),
        //    values...
        // }
        let tmp = self.generate_temp();
        
        func.assign_instr(
            tmp.clone(),
            qbe::Type::Long,
            Instr::Alloc8(
                qbe::Type::Long.size()
                    + if let Some(ref ty) = first_type {
                        ty.clone().into_qbe().size() * (len as u64)
                    } else {
                        0
                    },
            ),
        );
        
        func.add_instr(Instr::Store(
            qbe::Type::Long,
            tmp.clone(),
            Value::Const(len as u64),
        ));

        for (i, value) in results.iter().enumerate() {
            let value_ptr = self.generate_temp();
            
            func.assign_instr(
                value_ptr.clone(),
                qbe::Type::Long,
                Instr::Add(
                    tmp.clone(),
                    Value::Const(
                        qbe::Type::Long.size() + (i as u64) * first_type.as_ref().unwrap().clone().into_qbe().size(),
                    ),
                ),
            );

            func.add_instr(Instr::Store(
                first_type.as_ref().unwrap().clone().into_qbe(),
                value_ptr,
                value.to_owned(),
            ));
        }

        self.unique_name_counter += 1;
        
        let name = format!("array.{}", self.unique_name_counter);
        
        let typedef = TypeDef {
            name: name.clone(),
            align: None,
            items: if let Some(ty) = first_type.clone() {
                vec![(qbe::Type::Long, 1), (ty.into_qbe(), len as usize)]
            } else {
                // No elements
                vec![(qbe::Type::Long, 1)]
            },
        };
        
        self.typedefs.push(typedef);

        Ok((first_type.as_ref().unwrap().clone(), tmp))
    }

    fn generate_type(&mut self, ty: &ParseType) -> GenerationResult<Type> {
        TypeGenerator::generate_type(ty.clone(), self.clone())
    }

    fn generate_bin_op(
        &mut self,
        left: AstNode,
        op: String,
        right: AstNode,
        func: &mut Function<'a>,
    ) -> GenerationResult<ValuePair> {
        let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };
        let self3 = unsafe { (self as *mut Self).as_mut_unchecked() };

        let (left_t, left) = self2.generate_expr(left, func)?;
        let (right_t, right) = self3.generate_expr(right, func)?;

        match op.as_str() {
            "==" => {
                // Dealing with C strings
                if CSTRING_TYPES.contains(&&*left_t.to_string()) {
                    let cmp_fn = format!("{left_t}{right_t}eqcmp");

                    let tmp = self2.generate_temp();
                    let args: [(qbe::Type, Value); 2] = [
                        (left_t.into_qbe_abi(), left),
                        (right_t.into_qbe_abi(), right),
                    ];

                    func.assign_instr(
                        tmp.clone(),
                        Type::Integer8.into_qbe_abi(),
                        Instr::Call(cmp_fn, Vec::from(args)),
                    );

                    return Ok((Type::Integer8, tmp));
                } else if left_t.to_cmp_string() == "Fc".to_string() {
                    let cmp_fn = format!("{D}{D}eqcmp", D = left_t.to_cmp_string());

                    let Type::FatPointer(_, l) = left_t else {
                        unreachable!()
                    };

                    let Type::FatPointer(_, r) = right_t else {
                        unreachable!()
                    };

                    let tmp = self2.generate_temp();
                    let args: [(qbe::Type, Value); 4] = [
                        (Type::Integer32.into_qbe_abi(), Value::Const(l as u64)),
                        (left_t.into_qbe_abi(), left),
                        (Type::Integer32.into_qbe_abi(), Value::Const(r as u64)),
                        (right_t.into_qbe_abi(), right),
                    ];

                    func.assign_instr(
                        tmp.clone(),
                        Type::Integer8.into_qbe_abi(),
                        Instr::Call(cmp_fn, Vec::from(args)),
                    );

                    return Ok((Type::Integer8, tmp));
                }

                let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };

                let tmp = self2.generate_temp();

                func.assign_instr(
                    tmp.clone(),
                    Type::Integer8.into_qbe_abi(),
                    Instr::Cmp(left_t.into_qbe_abi(), Cmp::Eq, left, right),
                );

                Ok((Type::Integer8, tmp))
            }
            "!=" => {
                if left_t != right_t {
                    return Ok((Type::Integer8, Value::Const(1)));
                }

                let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };

                let tmp = self2.generate_temp();

                func.assign_instr(
                    tmp.clone(),
                    Type::Integer8.into_qbe_abi(),
                    Instr::Cmp(left_t.into_qbe_abi(), Cmp::Ne, left, right),
                );

                Ok((Type::Integer8, tmp))
            }
            op => Err(GenerationError::UndefinedSymbol(format!("operators::{op}"))),
        }
    }

    fn generate_expr(
        &mut self,
        expr: AstNode,
        func: &mut Function<'a>,
    ) -> GenerationResult<ValuePair> {
        match expr {
            AstNode::InfixOp(left, op, right) => {
                self.generate_bin_op(left.deref().clone(), op, right.deref().clone(), func)
            }
            AstNode::NumberLiteral(_)
            | AstNode::StringLiteral(_)
            | AstNode::BooleanLiteral(_)
            | AstNode::NullLiteral
            | AstNode::Identifier(_) => self.generate_independent_expr(expr),
            AstNode::AsExpr(left, to) => {
                let (ty, left) = self.generate_expr(left.as_ref().clone(), func)?;
                let to = self.generate_type(&to)?;

                match ty {
                    Type::FatPointer(_, _) => {
                        return match to {
                            // converting *L[i8] to *i8
                            Type::Pointer(t) if matches!(t.deref(), Type::Integer8) => {
                                let Value::Global(name) = left else {
                                    unreachable!()
                                };

                                let mut matched = self
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
                                    .push((Type::Integer8.into_qbe_abi(), DataItem::Const(0)));

                                self.datadefs.push(def);

                                Ok((Type::Pointer(t), Value::Global(name)))
                            }
                            // converting *L[i8] to *:0[i8]
                            Type::TerminatedSlice(t, e)
                                if matches!(t.deref(), Type::Integer8) && e == Value::Const(0) =>
                            {
                                let Value::Global(name) = left else {
                                    unreachable!()
                                };

                                let mut matched = self
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
                                    .push((Type::Integer8.into_qbe_abi(), DataItem::Const(0)));

                                self.datadefs.push(def);

                                Ok((Type::TerminatedSlice(t, e), Value::Global(name)))
                            }
                            t => Err(GenerationError::InvalidCast(ty, t)),
                        };
                    }
                    // converting *:0[i8] to *i8
                    Type::TerminatedSlice(t, e) if e == Value::Const(0) => {
                        Ok((Type::Pointer(t), left))
                    }
                    t => Err(GenerationError::InvalidCast(t, to)),
                }
            }
            AstNode::ArrayLiteral(els) => self.generate_array(func, els.len() as u32, els),
            AstNode::PrefixOp(_, _) => todo!(),
            AstNode::PostfixOp(_, _) => todo!(),
            AstNode::MemberExpr(_) => todo!(),
            AstNode::IdxAccess(left, i) => {
                let (ty, left) = self.generate_expr(left.deref().clone(), func)?;
                
                match ty {
                    Type::Pointer(inner) => {
                        let addr = self.generate_temp();

                        let offset = i as u64 * inner.deref().clone().into_qbe().size();

                        println!("{offset}");

                        func.assign_instr(
                            addr.clone(),
                            Type::Integer64.into_qbe_abi(),
                            Instr::Add(left, Value::Const(offset)),
                        );

                        let loaded = self.generate_temp();

                        let qbe_inner = inner.deref().clone().into_qbe_abi();

                        func.assign_instr(
                            loaded.clone(),
                            qbe_inner.clone(),
                            Instr::Load(qbe_inner.clone(), addr),
                        );

                        Ok((inner.deref().clone(), loaded))
                    },
                    t => Err(GenerationError::CannotIndex(t))
                }
            }
            AstNode::CallExpr { callee, args } => {
                let mut new_args: Vec<(qbe::Type, Value)> = Vec::new();

                for arg in args.iter() {
                    let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };

                    let (ty, v) = self2.generate_expr(arg.clone(), func)?;

                    new_args.push((ty.into_qbe_abi(), v));
                }

                let tmp = self.generate_temp();

                let AstNode::Identifier(name) = callee.as_ref().clone() else {
                    todo!("Implement member-expression calls")
                };

                let Some(f) = self.functions.get(&name) else {
                    return Err(GenerationError::UndefinedSymbol(name.clone()));
                };

                func.assign_instr(
                    tmp.clone(),
                    f.0.clone().into_qbe_abi(),
                    Instr::Call(name, new_args),
                );

                Ok((Type::Integer32, tmp))
            }
            AstNode::IfExpr {
                cond,
                block,
                else_clause,
            } => {
                self.unique_name_counter += 1;

                let (_, cond) = self.generate_expr(cond.deref().clone(), func)?;

                let if_label = format!("cond.if.{C}", C = self.unique_name_counter);
                let else_label = format!("cond.else.{C}", C = self.unique_name_counter);
                let end_label = format!("cond.end.{C}", C = self.unique_name_counter);

                let result = self.generate_temp();
                let mut result_type = Type::Integer8;

                func.add_instr(Instr::Jnz(cond, if_label.clone(), else_label.clone()));

                func.add_block(else_label);

                let ParseBlock::Plain(else_clause) = else_clause;

                for (i, stmt) in else_clause.iter().enumerate() {
                    if i == else_clause.len() - 1 {
                        let (ty, r) = self.generate_expr(stmt.clone(), func)?;

                        result_type = ty.clone();

                        func.assign_instr(result.clone(), ty.into_qbe_abi(), Instr::Copy(r));

                        break;
                    }

                    self.generate_expr(stmt.clone(), func)?;
                }

                func.add_instr(Instr::Jmp(end_label.clone()));

                func.add_block(if_label);

                let ParseBlock::Plain(block) = block;

                for (i, stmt) in block.iter().enumerate() {
                    if i == block.len() - 1 {
                        let (ty, r) = self.generate_expr(stmt.clone(), func)?;

                        result_type = ty.clone();

                        func.assign_instr(result.clone(), ty.into_qbe_abi(), Instr::Copy(r));

                        break;
                    }

                    self.generate_expr(stmt.clone(), func)?;
                }

                func.add_block(end_label);

                Ok((result_type, result))
            }
            stmt => {
                self.generate_stmt(stmt, func)?;

                Ok((Type::Integer8, Value::Const(0)))
            }
        }
    }

    fn generate_func(
        &mut self,
        name: String,
        ret_type: Type,
        args: Box<[ArgMeta]>,
        code: ParseBlock,
    ) -> GenerationResult<Function<'a>> {
        self.scopes.push(Default::default());

        let mut arguments: Vec<(qbe::Type, Value)> = Vec::new();

        for (name, r#type, _) in args.clone() {
            let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };

            let tmp = self2.declare_var(r#type.clone(), name)?;

            arguments.push((r#type.into_qbe_abi(), tmp));
        }

        let mut func = Function {
            linkage: qbe::Linkage::public(),
            name: name.clone(),
            arguments,
            return_ty: Some(ret_type.clone().into_qbe_abi()),
            blocks: Vec::new(),
        };

        func.add_block("start");

        let ParseBlock::Plain(code) = code;

        for expr in code {
            let self2 = unsafe { (self as *mut Self).as_mut_unchecked() };

            self2.generate_expr(expr, &mut func)?;
        }

        self.functions.insert(name, (ret_type, args));

        self.module.add_function(func.clone());

        Ok(func)
    }

    fn generate_independent_expr(&mut self, expr: AstNode) -> GenerationResult<ValuePair> {
        match expr {
            AstNode::NumberLiteral(n) => {
                if n.fract() == 0f64 {
                    let value = Value::Const(n as u64);
                    Ok((Type::Integer32, value))
                } else {
                    let value = Value::Const(u64::from_be_bytes(n.to_be_bytes()));
                    Ok((Type::Float64, value))
                }
            }
            AstNode::StringLiteral(s) => self.generate_string(s),
            AstNode::BooleanLiteral(b) => Ok((Type::Boolean, Value::Const(b as u64))),
            AstNode::NullLiteral => Ok((Type::NullVoid, Value::Const(0))),
            AstNode::Identifier(name) => {
                let v = self.get_var(name)?;

                Ok(v.clone())
            }
            _ => unimplemented!(),
        }
    }

    fn generate_stmt(&mut self, stmt: AstNode, func: &mut Function<'a>) -> GenerationResult<()> {
        match stmt {
            AstNode::ReturnStmt(v) => {
                let instr = Instr::Ret(Some(self.generate_expr(v.deref().clone(), func)?.1));

                func.add_instr(instr)
            }
            AstNode::IfStmt { cond, block } => {
                self.unique_name_counter += 1;

                let (_, cond) = self.generate_expr(cond.deref().clone(), func)?;

                let if_label = format!("cond.if.{C}", C = self.unique_name_counter);
                let end_label = format!("cond.end.{C}", C = self.unique_name_counter);

                func.add_instr(Instr::Jnz(cond, if_label.clone(), end_label.clone()));

                func.add_block(if_label);

                let ParseBlock::Plain(block) = block;

                for stmt in block {
                    self.generate_expr(stmt, func)?;
                }

                func.add_block(end_label);
            }
            AstNode::DefStmt {
                name,
                value,
                def_type,
            } => {
                // TODO: Type Checking

                let (_, value) = self.generate_expr(value.deref().clone(), func)?;

                let ty = self.generate_type(&def_type)?;
                let tmp = self.declare_var(ty.clone(), name)?;

                func.assign_instr(tmp, ty.clone().into_qbe_abi(), Instr::Copy(value))
            }
            _ => unimplemented!("Compile statement {stmt}"),
        }

        Ok(())
    }

    fn generate_global_stmt(&mut self, code: Box<[AstNode]>) -> GenerationResult<()> {
        for stmt in code {
            match stmt {
                AstNode::DefStmt { .. } => todo!(),
                AstNode::IncludeStmt(p) => {
                    let AstNode::Path(p) = p.as_ref() else {
                        unreachable!()
                    };

                    let search_path = p.as_ref().split_last().unwrap().1.join("/");

                    if search_path.is_empty() {
                        let msc_path = PathBuf::from(format!("./{}.msc", p.last().unwrap()));
                        let obj_path = PathBuf::from(format!("./{}.o", p.last().unwrap()));

                        fs::File::open(msc_path.clone()).map_err(|_| {
                            GenerationError::UndefinedLibrary(
                                format!("./{}", p.last().unwrap()).parse().unwrap(),
                            )
                        })?;

                        if fs::File::open(obj_path.clone()).is_ok() {
                            self.used_modules
                                .push(MosaicModule::new_external(obj_path, msc_path));
                        } else {
                            self.used_modules.push(MosaicModule::new_native(msc_path));
                        }

                        return Ok(());
                    }

                    let mut msc_path =
                        PathBuf::from(format!("{search_path}/{}.msc", p.last().unwrap()));
                    let mut obj_path =
                        PathBuf::from(format!("{search_path}/{}.o", p.last().unwrap()));

                    // Attempt lookup in installed modules directory (~/.msc/mods/)
                    if fs::File::open(msc_path.clone()).is_err() {
                        let home = std::env::var("HOME").unwrap();

                        msc_path = PathBuf::from(format!(
                            "{home}/.msc/mods/{search_path}/{}.msc",
                            p.last().unwrap()
                        ));
                        obj_path = PathBuf::from(format!(
                            "{home}/.msc/mods/{search_path}/{}.o",
                            p.last().unwrap()
                        ));
                    }

                    // SHADOW CODEGEN

                    let reader =
                        CharReader::new(File::new(msc_path.to_str().unwrap().to_string()).unwrap());

                    let lexer = StreamedLexer::new(reader);
                    let mut parser = StreamedParser::new(lexer);

                    let mut nodes: Vec<AstNode> = vec![];

                    while let Some(node) = parser.next_ast_node() {
                        nodes.push(node.unwrap())
                    }

                    // Compile module and add functions, datadefs, etc… to current cg

                    let mut shadow_cg = CodeGen::new(nodes.into_boxed_slice());

                    shadow_cg.unique_name_counter = self.unique_name_counter + 1;

                    shadow_cg.generate()?;

                    for (name, meta) in shadow_cg.functions {
                        if !self.functions.contains_key(&name) {
                            self.functions.insert(name, meta);
                        }
                    }

                    for (name, ty) in shadow_cg.types {
                        if !self.functions.contains_key(&name) {
                            self.types.insert(name, ty);
                        }
                    }

                    for def in shadow_cg.datadefs {
                        if !self.datadefs.contains(&def) {
                            self.datadefs.push(def);
                        }
                    }

                    for module in shadow_cg.used_modules {
                        if !self.used_modules.contains(&module) {
                            self.used_modules.push(module);
                        }
                    }

                    self.unique_name_counter = shadow_cg.unique_name_counter + 1;

                    fs::File::open(msc_path.clone()).map_err(|_| {
                        GenerationError::UndefinedLibrary(
                            format!("{}::{}", search_path.replace("/", "::"), p.last().unwrap())
                                .parse()
                                .unwrap(),
                        )
                    })?;

                    if fs::File::open(obj_path.clone()).is_ok() {
                        self.used_modules
                            .push(MosaicModule::new_external(obj_path, msc_path));
                    } else {
                        self.used_modules.push(MosaicModule::new_native(msc_path));
                    }
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
                                TypeGenerator::generate_type(r#type.clone(), self.clone())
                                    .unwrap()
                                    .clone(),
                                None,
                            )
                        })
                        .collect();
                    let r#type = TypeGenerator::generate_type(ret_type.clone(), self.clone())?;

                    self.functions
                        .insert(name.clone(), (r#type, args.into_boxed_slice()));
                }
                AstNode::Program(_) => unreachable!(),
                AstNode::FnExpr {
                    name,
                    ret_type,
                    args,
                    code,
                } => {
                    let args: Vec<ArgMeta> = args
                        .into_iter()
                        .map(|(name, r#type, _default)| {
                            (
                                name.clone(),
                                TypeGenerator::generate_type(r#type.clone(), self.clone())
                                    .unwrap()
                                    .clone(),
                                None,
                            )
                        })
                        .collect();
                    let r#type = TypeGenerator::generate_type(ret_type.clone(), self.clone())?;

                    self.generate_func(
                        name.clone(),
                        r#type,
                        args.into_boxed_slice(),
                        code.clone(),
                    )?;
                }
                stmt => unimplemented!("Compile statement {stmt}"),
            }
        }

        Ok(())
    }

    pub fn generate(&mut self) -> GenerationResult<Module<'a>> {
        self.generate_global_stmt(self.code.clone())?;

        for def in self.datadefs.iter() {
            self.module.add_data(def.clone());
        }

        Ok(self.module.clone())
    }

    pub fn new(code: Box<[AstNode]>) -> Self {
        Self {
            unique_name_counter: 0,
            module: Default::default(),
            types: HashMap::from([
                ("i8".into(), Type::Integer8),
                ("i16".into(), Type::Integer16),
                ("i32".into(), Type::Integer32),
                ("i64".into(), Type::Integer64),
                (
                    "u8".into(),
                    Type::Unsigned(Indirection::new(Type::Integer8)),
                ),
                (
                    "u16".into(),
                    Type::Unsigned(Indirection::new(Type::Integer16)),
                ),
                ("bool".into(), Type::Boolean),
                ("f32".into(), Type::Float32),
                ("f64".into(), Type::Float64),
                ("null".into(), Type::NullVoid),
            ]),
            scopes: vec![],
            functions: Default::default(),
            datadefs: vec![],
            code,
            used_modules: vec![],
            typedefs: vec![],
        }
    }
}
