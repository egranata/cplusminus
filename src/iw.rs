// Copyright 2023 Enrico Granata
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use inkwell::{
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{Target, TargetMachine, TargetTriple},
    types::{BasicTypeEnum, FloatType, IntType, VoidType},
    values::{BasicValueEnum, FloatValue, FunctionValue, GlobalValue, IntValue},
};
use peg::{error::ParseError, str::LineCol};
use std::{
    cell::RefCell,
    collections::HashMap,
    path::{Path, PathBuf},
    process::Command,
    rc::Rc,
};

use crate::{
    ast::{Location, ProperStructDecl, RawStructDecl, TopLevelDecl, TopLevelDeclaration},
    bom::{
        alias::AliasBomEntry, function::FunctionBomEntry, module::BillOfMaterials,
        variable::VariableBomEntry,
    },
    builders::{
        func::{FunctionBuilder, FunctionBuilderOptions},
        refcount::Refcounting,
        scope::{Scope, ScopeObject, VarInfo},
        ty::TypeBuilder,
    },
    err::{CompilerDiagnostic, CompilerError, CompilerWarning, Error},
    parser::cpm::source_file,
};

use crate::codegen::{structure::Structure, MutableOf};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

#[derive(Clone)]
pub struct Input {
    pub path: PathBuf,
    pub content: String,
}

impl Input {
    #[allow(clippy::result_unit_err)]
    pub fn file_in_input_path(&self, name: &str) -> Result<PathBuf, ()> {
        if self.path.exists() {
            // if this path exists, expect the parent to exist too
            Ok(self.path.parent().unwrap().join(name))
        } else {
            Err(())
        }
    }

    pub fn from_string(content: &str) -> Self {
        Self {
            path: PathBuf::new(),
            content: content.to_string(),
        }
    }

    pub fn from_file(path: &Path) -> Self {
        Self {
            path: path.to_path_buf(),
            content: std::fs::read_to_string(path).unwrap(),
        }
    }

    pub fn path_to_string(&self) -> String {
        if self.path.exists() {
            self.path.to_str().unwrap().to_owned()
        } else {
            String::from("<unknown buffer>")
        }
    }
}

#[derive(Clone)]
pub struct CompilerOptions {
    pub triple: String,
    pub warn_as_err: bool,
    pub instrument_refcount: bool,
    pub link_extras: Vec<String>,
    pub dump_ir_text: bool,
    pub dump_bom: bool,
    pub optimize: bool,
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            triple: String::from("x86_64-pc-linux-gnu"),
            warn_as_err: false,
            instrument_refcount: false,
            link_extras: vec![],
            dump_ir_text: false,
            dump_bom: false,
            optimize: false,
        }
    }
}

impl CompilerOptions {
    pub fn unoptimized() -> Self {
        Default::default()
    }

    pub fn optimized() -> Self {
        Self {
            optimize: true,
            ..Default::default()
        }
    }
}

#[derive(Clone, Copy)]
pub struct BuiltinTypes<'a> {
    pub bool: IntType<'a>,
    pub byte: IntType<'a>,
    pub int32: IntType<'a>,
    pub int64: IntType<'a>,
    pub float32: FloatType<'a>,
    pub float64: FloatType<'a>,
    pub void: VoidType<'a>,
    pub default_int_type: IntType<'a>,
    pub default_float_type: FloatType<'a>,
}

impl<'a> BuiltinTypes<'a> {
    pub fn new(c: &'a Context) -> Self {
        Self {
            bool: c.bool_type(),
            byte: c.i8_type(),
            int32: c.i32_type(),
            int64: c.i64_type(),
            float32: c.f32_type(),
            float64: c.f64_type(),
            void: c.void_type(),
            default_int_type: c.i64_type(),
            default_float_type: c.f64_type(),
        }
    }

    pub fn zero(&self, i: IntType<'a>) -> IntValue<'a> {
        i.const_zero()
    }

    pub fn one(&self, i: IntType<'a>) -> IntValue<'a> {
        self.n(1, i)
    }

    pub fn n(&self, val: u64, i: IntType<'a>) -> IntValue<'a> {
        i.const_int(val, false)
    }

    pub fn flt_zero(&self, i: FloatType<'a>) -> FloatValue<'a> {
        i.const_zero()
    }

    pub fn flt_one(&self, i: FloatType<'a>) -> FloatValue<'a> {
        self.flt_n(1.0, i)
    }

    pub fn flt_n(&self, val: f64, i: FloatType<'a>) -> FloatValue<'a> {
        i.const_float(val)
    }
}

#[derive(Clone)]
pub struct CompilerCore<'a> {
    pub context: &'a Context,
    pub refcnt: Refcounting<'a>,
    pub module: Rc<Module<'a>>,
    pub target: Rc<Target>,
    pub machine: Rc<TargetMachine>,
    pub source: Input,
    pub options: CompilerOptions,
    pub structs: MutableOf<HashMap<String, Structure<'a>>>,
    pub diagnostics: MutableOf<Vec<CompilerDiagnostic>>,
    pub builtins: BuiltinTypes<'a>,
    pub globals: Scope<'a>,
    pub bom: MutableOf<BillOfMaterials>,
}

impl<'a> CompilerCore<'a> {
    pub fn new(context: &'a Context, src: &Input, options: CompilerOptions) -> CompilerCore<'a> {
        let triple = TargetTriple::create(&options.triple);
        let module = Rc::new(context.create_module(""));
        module.set_triple(&triple);

        Target::initialize_all(&Default::default());
        let target = Target::from_triple(&triple).expect("unable to create a target");
        let tm = target
            .create_target_machine(
                &triple,
                Default::default(),
                Default::default(),
                Default::default(),
                inkwell::targets::RelocMode::PIC,
                inkwell::targets::CodeModel::Default,
            )
            .expect("unable to create a target machine");

        CompilerCore::fill_globals(&module, context);
        let refcnt = CompilerCore::fill_refcounting(&module, context, &options);
        let new = Self {
            context,
            refcnt,
            module,
            target: Rc::from(target),
            machine: Rc::from(tm),
            source: src.clone(),
            options,
            structs: Rc::new(RefCell::new(HashMap::new())),
            diagnostics: Rc::new(RefCell::new(Vec::new())),
            builtins: BuiltinTypes::new(context),
            globals: ScopeObject::root(),
            bom: Default::default(),
        };
        new.fill_default_types();
        new.forbid_32bit_targets();
        new
    }

    fn forbid_32bit_targets(&self) {
        if self.machine.get_target_data().get_pointer_byte_size(None) != 8 {
            self.error(CompilerError::unbound(Error::ThirtyTwoBitUnsupported));
        }
    }

    fn fill_default_types(&self) {
        use BasicTypeEnum::*;

        self.globals
            .insert_alias("byte", IntType(self.builtins.byte), true);
        self.globals
            .insert_alias("int32", IntType(self.builtins.int32), true);
        self.globals
            .insert_alias("int64", IntType(self.builtins.int64), true);
        self.globals
            .insert_alias("float64", FloatType(self.builtins.float64), true);
        self.globals
            .insert_alias("float32", FloatType(self.builtins.float32), true);
        self.globals
            .insert_alias("bool", IntType(self.builtins.bool), true);
    }

    pub fn make_global(
        m: &Module<'a>,
        name: &str,
        ty: BasicTypeEnum<'a>,
        val: Option<BasicValueEnum<'a>>,
        lnk: Linkage,
    ) -> GlobalValue<'a> {
        let global = m.add_global(ty, Default::default(), name);
        if let Some(val) = val {
            global.set_initializer(&val);
        }
        global.set_linkage(lnk);
        global
    }

    fn fill_globals(m: &Module<'a>, c: &'a Context) {
        let bt = c.bool_type();
        let i64 = c.i64_type();
        let void = c.void_type();

        let itstrue = BasicValueEnum::IntValue(bt.const_int(1, false));
        let itsfalse = BasicValueEnum::IntValue(bt.const_int(0, false));
        let itszero = BasicValueEnum::IntValue(i64.const_zero());

        CompilerCore::make_global(
            m,
            "true",
            itstrue.get_type(),
            Some(itstrue),
            Linkage::Internal,
        );
        CompilerCore::make_global(
            m,
            "false",
            itsfalse.get_type(),
            Some(itsfalse),
            Linkage::Internal,
        );
        CompilerCore::make_global(
            m,
            "g_FreedObjects",
            itszero.get_type(),
            Some(itszero),
            Linkage::Internal,
        );

        let trap_type = void.fn_type(&[], false);
        m.add_function("llvm.trap", trap_type, Some(Linkage::Internal));
    }

    fn fill_refcounting(
        m: &Module<'a>,
        c: &'a Context,
        options: &CompilerOptions,
    ) -> Refcounting<'a> {
        crate::builders::refcount::build_refcount_apis(m, c, options)
    }

    fn parse(&self) -> Result<Vec<TopLevelDeclaration>, ParseError<LineCol>> {
        source_file(&self.source.content)
    }

    fn fixup_struct_decl(&self, raw: &RawStructDecl) -> Option<ProperStructDecl> {
        let mut proper = ProperStructDecl {
            loc: raw.loc,
            name: raw.name.clone(),
            ms: raw.ms,
            fields: vec![],
            init: None,
            dealloc: None,
        };

        for entry in &raw.entries {
            match entry {
                crate::ast::StructEntryDecl::Field(field) => proper.fields.push(field.clone()),
                crate::ast::StructEntryDecl::Init(init) => {
                    if proper.init.is_some() {
                        self.error(CompilerError::new(
                            init.loc,
                            Error::DuplicatedStructMember("init".to_owned()),
                        ));
                        return None;
                    } else {
                        proper.init = Some(init.clone());
                    }
                }
                crate::ast::StructEntryDecl::Dealloc(dealloc) => {
                    if proper.dealloc.is_some() {
                        self.error(CompilerError::new(
                            dealloc.loc,
                            Error::DuplicatedStructMember("dealloc".to_owned()),
                        ));
                        return None;
                    } else {
                        proper.dealloc = Some(dealloc.clone());
                    }
                }
            }
        }

        Some(proper)
    }

    fn check_ast_decl(&self, tld: &TopLevelDecl) -> bool {
        match tld {
            TopLevelDecl::Structure(sd) => {
                for entry_decl in &sd.entries {
                    match entry_decl {
                        crate::ast::StructEntryDecl::Field(field_decl) => {
                            if field_decl.name.starts_with("__") {
                                self.error(CompilerError::new(
                                    field_decl.loc,
                                    Error::ReservedIdentifier(field_decl.name.clone()),
                                ));
                                return false;
                            }
                        }
                        crate::ast::StructEntryDecl::Init(..)
                        | crate::ast::StructEntryDecl::Dealloc(..) => {}
                    }
                }
                true
            }
            TopLevelDecl::Function(fd) => {
                if fd.decl.name.starts_with("__") {
                    self.error(CompilerError::new(
                        fd.decl.loc,
                        Error::ReservedIdentifier(fd.decl.name.clone()),
                    ));
                    false
                } else {
                    true
                }
            }
            TopLevelDecl::Extern(fd) => {
                if fd.decl.name.starts_with("__") {
                    self.error(CompilerError::new(
                        fd.loc,
                        Error::ReservedIdentifier(fd.decl.name.clone()),
                    ));
                    false
                } else {
                    true
                }
            }
            TopLevelDecl::Alias(ad) => {
                if ad.name.starts_with("__") {
                    self.error(CompilerError::new(
                        ad.loc,
                        Error::ReservedIdentifier(ad.name.clone()),
                    ));
                    false
                } else {
                    true
                }
            }
            _ => true,
        }
    }

    fn import(&self, bom: &BillOfMaterials) {
        for ta in &bom.aliases {
            ta.import(self, &self.globals);
        }
        for ef in &bom.functions {
            ef.import(self, &self.globals);
        }
        for gv in &bom.variables {
            gv.import(self, &self.globals);
        }
    }

    pub fn compile(&self) -> bool {
        let parsed = self.parse();
        match parsed {
            Ok(tlds) => {
                for tld in &tlds {
                    if !self.check_ast_decl(&tld.payload) {
                        continue;
                    }

                    match &tld.payload {
                        crate::ast::TopLevelDecl::Function(fd) => {
                            let fb = FunctionBuilder::new(self.clone());
                            let opts = FunctionBuilderOptions::default()
                                .extrn(false)
                                .global(true)
                                .mangle(false)
                                .export(fd.export)
                                .commit();
                            fb.declare(&self.globals, &fd.decl, opts);
                        }
                        crate::ast::TopLevelDecl::Extern(fd) => {
                            let fb = FunctionBuilder::new(self.clone());
                            let opts = FunctionBuilderOptions::default()
                                .extrn(true)
                                .global(true)
                                .mangle(false)
                                .export(false)
                                .commit();
                            if let Some(fv) = fb.declare(&self.globals, &fd.decl, opts) {
                                if fd.export {
                                    let bom_entry = FunctionBomEntry::new(&fd.decl.name, fv);
                                    self.bom.borrow_mut().functions.push(bom_entry);
                                }
                            }
                        }
                        crate::ast::TopLevelDecl::Structure(sd) => {
                            let ty = TypeBuilder::new(self.clone());
                            if let Some(psd) = self.fixup_struct_decl(sd) {
                                if ty.build_structure_from_decl(&self.globals, &psd).is_none() {
                                    self.error(CompilerError::new(
                                        sd.loc,
                                        Error::InvalidExpression,
                                    ));
                                }
                            } else {
                                self.error(CompilerError::new(sd.loc, Error::InvalidExpression));
                            }
                        }
                        crate::ast::TopLevelDecl::Alias(ad) => {
                            let ty = TypeBuilder::new(self.clone());
                            if let Some(uty) = ty.alias(&self.globals, &ad.name, &ad.ty) {
                                if ad.export {
                                    // we just generated this from a descriptor, assume roundtrip is safe
                                    let utd = TypeBuilder::descriptor_by_llvm_type(uty).unwrap();
                                    let bom_entry = AliasBomEntry::new(&ad.name, &utd);
                                    self.bom.borrow_mut().aliases.push(bom_entry);
                                }
                            } else {
                                self.error(CompilerError::new(ad.loc, Error::InvalidExpression));
                            }
                        }
                        crate::ast::TopLevelDecl::Implementation(id) => {
                            let tb = TypeBuilder::new(self.clone());
                            if let Some(ty) = tb.llvm_type_by_descriptor(&self.globals, &id.of) {
                                if let Some(sty) = tb.is_val_or_ref_basic_type(ty) {
                                    if let Some(struct_info) = tb.struct_by_name(sty) {
                                        tb.build_impl(&self.globals, &struct_info, id);
                                    } else {
                                        self.error(CompilerError::new(
                                            id.loc,
                                            Error::TypeNotFound(id.of.clone()),
                                        ));
                                    }
                                } else {
                                    self.error(CompilerError::new(
                                        id.loc,
                                        Error::UnexpectedType(Some("structure".to_owned())),
                                    ));
                                }
                            }
                        }
                        crate::ast::TopLevelDecl::Import(id) => {
                            let bom_path = self
                                .source
                                .file_in_input_path(&id.path)
                                .unwrap_or(PathBuf::from(&id.path));
                            if let Some(bom) = BillOfMaterials::load(bom_path.as_path()) {
                                self.import(&bom);
                            } else {
                                self.error(CompilerError::new(
                                    tld.loc,
                                    Error::InternalError(String::from("unable to find BOM")),
                                ));
                            }
                        }
                        crate::ast::TopLevelDecl::Variable(gvd) => {
                            let vd = &gvd.decl;
                            if vd.val.is_some() {
                                self.error(CompilerError::new(
                                    gvd.loc,
                                    Error::InternalError(String::from(
                                        "globals cannot be initialized",
                                    )),
                                ));
                            } else if !vd.rw {
                                self.error(CompilerError::new(
                                    gvd.loc,
                                    Error::InternalError(String::from(
                                        "globals cannot be read-only",
                                    )),
                                ));
                            } else if vd.ty.is_none() {
                                self.error(CompilerError::new(
                                    gvd.loc,
                                    Error::InternalError(String::from(
                                        "globals must be explicitly typed",
                                    )),
                                ));
                            } else {
                                let tb = TypeBuilder::new(self.clone());
                                if let Some(var_type) = tb
                                    .llvm_type_by_descriptor(&self.globals, vd.ty.as_ref().unwrap())
                                {
                                    let global = CompilerCore::make_global(
                                        &self.module,
                                        &vd.name,
                                        var_type,
                                        Some(TypeBuilder::zero_for_type(var_type)),
                                        if gvd.export {
                                            Linkage::External
                                        } else {
                                            Linkage::Internal
                                        },
                                    );

                                    let vi = VarInfo::new(
                                        tld.loc,
                                        vd.name.clone(),
                                        global.as_pointer_value(),
                                        true,
                                    );
                                    self.globals.insert_variable(&vd.name, vi, true);

                                    if gvd.export {
                                        let bom_entry = VariableBomEntry::new(
                                            global.get_name().to_str().unwrap(),
                                            vd.ty.as_ref().unwrap(),
                                        );
                                        self.bom.borrow_mut().variables.push(bom_entry);
                                    }
                                } else {
                                    self.error(CompilerError::new(
                                        gvd.loc,
                                        Error::TypeNotFound(vd.ty.as_ref().unwrap().clone()),
                                    ));
                                }
                            }
                        }
                    }
                }

                for tld in &tlds {
                    match &tld.payload {
                        crate::ast::TopLevelDecl::Function(fd) => {
                            let fb = FunctionBuilder::new(self.clone());
                            fb.build(&self.globals, fd);
                        }

                        crate::ast::TopLevelDecl::Alias(..)
                        | crate::ast::TopLevelDecl::Extern(..)
                        | crate::ast::TopLevelDecl::Implementation(..)
                        | crate::ast::TopLevelDecl::Import(..)
                        | crate::ast::TopLevelDecl::Structure(..)
                        | crate::ast::TopLevelDecl::Variable(..) => {}
                    }
                }
            }
            Err(err) => {
                let loc = Location {
                    start: err.location.offset,
                    end: err.location.offset + 1,
                };
                self.error(CompilerError::new(
                    loc,
                    Error::ParseError(err.expected.to_string()),
                ));
            }
        };

        self.success()
    }

    pub fn run_passes(&self) {
        let pmb = PassManagerBuilder::create();
        pmb.set_optimization_level(inkwell::OptimizationLevel::Aggressive);

        let func_pass: PassManager<FunctionValue> = PassManager::create(self.module.as_ref());
        let module_pass: PassManager<Module> = PassManager::create(());
        let lto_pass: PassManager<Module> = PassManager::create(());

        pmb.populate_function_pass_manager(&func_pass);
        pmb.populate_module_pass_manager(&module_pass);
        pmb.populate_lto_pass_manager(&lto_pass, true, true);

        self.module.get_functions().for_each(|func| {
            func_pass.run_on(&func);
        });
        module_pass.run_on(&self.module);
        lto_pass.run_on(&self.module);
    }

    fn dump_to_ir(&self, out: &Path) {
        let _ = self.module.print_to_file(out);
    }

    fn dump_to_bc(&self, out: &Path) {
        self.module.write_bitcode_to_path(out);
    }

    fn dump_to_asm(&self, out: &Path) {
        let _ = self
            .machine
            .write_to_file(&self.module, inkwell::targets::FileType::Assembly, out);
    }

    fn dump_to_obj(&self, out: &Path) {
        let _ = self
            .machine
            .write_to_file(&self.module, inkwell::targets::FileType::Object, out);
    }

    fn dump_to_binary(&self, out: &Path) {
        if let Ok(temp_obj_file) = tempfile::NamedTempFile::new() {
            let temp_obj_path = temp_obj_file.path();
            self.dump_to_obj(temp_obj_path);

            let mut clang = Command::new("clang");
            clang
                .arg("-fPIC")
                .arg(temp_obj_path.as_os_str().to_str().unwrap())
                .arg("-o")
                .arg(out.as_os_str().to_str().unwrap());

            self.options
                .link_extras
                .iter()
                .map(|item| format!("-l{item}"))
                .for_each(|item| {
                    clang.arg(&item);
                });

            let process = clang.spawn();
            if let Ok(mut child) = process {
                match child.wait() {
                    Ok(_) => {}
                    Err(err) => {
                        panic!("compilation failed: {err}");
                    }
                }
            } else {
                panic!("unable to spawn system compiler; consider installing clang");
            }
        } else {
            panic!("unable to create a temporary file");
        }
    }

    pub fn dump(&self, path: &Path) {
        let ext = path.extension().map(|osstr| osstr.to_str().unwrap());
        match ext {
            Some("ir") => self.dump_to_ir(path),
            Some("ll") => self.dump_to_bc(path),
            Some("asm") => self.dump_to_asm(path),
            Some("obj") => self.dump_to_obj(path),
            _ => self.dump_to_binary(path),
        }
    }

    pub fn dump_bom(&self, path: &Path) {
        self.bom.borrow().write(path);
    }

    pub fn add_struct(&self, sd: &Structure<'a>) {
        self.structs
            .borrow_mut()
            .insert(sd.name.clone(), sd.clone());
    }

    pub fn error(&self, err: CompilerError) {
        self.diagnostics
            .borrow_mut()
            .push(CompilerDiagnostic::Error(err))
    }

    pub fn warning(&self, warn: CompilerWarning) {
        if self.options.warn_as_err {
            let err = CompilerError {
                loc: warn.loc,
                err: Error::WarningAsError(warn.warn),
            };
            self.diagnostics
                .borrow_mut()
                .push(CompilerDiagnostic::Error(err));
        } else {
            self.diagnostics
                .borrow_mut()
                .push(CompilerDiagnostic::Warning(warn))
        }
    }

    pub fn errors(&self) -> Vec<CompilerError> {
        self.diagnostics
            .borrow()
            .iter()
            .filter(|cd| matches!(cd, CompilerDiagnostic::Error(_)))
            .map(|cd| match cd {
                CompilerDiagnostic::Error(err) => err.clone(),
                _ => panic!(""),
            })
            .collect()
    }

    pub fn warnings(&self) -> Vec<CompilerWarning> {
        self.diagnostics
            .borrow()
            .iter()
            .filter(|cd| matches!(cd, CompilerDiagnostic::Warning(_)))
            .map(|cd| match cd {
                CompilerDiagnostic::Warning(warn) => warn.clone(),
                _ => panic!(""),
            })
            .collect()
    }

    pub fn success(&self) -> bool {
        self.errors().is_empty()
    }

    pub fn display_diagnostics(&self) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(self.source.path_to_string(), &self.source.content);
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        for diag in self.diagnostics.borrow().iter() {
            let diagnostic = match diag {
                CompilerDiagnostic::Error(err) => Diagnostic::error()
                    .with_message(format!("{}", err.err))
                    .with_labels(vec![Label::primary(file_id, err.loc.start..err.loc.end)]),
                CompilerDiagnostic::Warning(warn) => Diagnostic::warning()
                    .with_message(format!("{}", warn.warn))
                    .with_labels(vec![Label::primary(file_id, warn.loc.start..warn.loc.end)]),
            };

            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic)
                .expect("<io error>");
        }
    }

    pub fn display_errors(&self) {
        let mut files = SimpleFiles::new();

        let file_id = files.add(self.source.path_to_string(), &self.source.content);

        for err in &self.errors() {
            let diagnostic = Diagnostic::error()
                .with_message(format!("{}", err.err))
                .with_labels(vec![Label::primary(file_id, err.loc.start..err.loc.end)]);
            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();
            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic)
                .expect("<io error>");
        }
    }

    pub fn display_warnings(&self) {
        let mut files = SimpleFiles::new();

        let file_id = files.add(self.source.path_to_string(), &self.source.content);

        for warn in &self.warnings() {
            let diagnostic = Diagnostic::warning()
                .with_message(format!("{}", warn.warn))
                .with_labels(vec![Label::primary(file_id, warn.loc.start..warn.loc.end)]);
            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();
            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic)
                .expect("<io error>");
        }
    }
}
