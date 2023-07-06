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
    targets::{Target, TargetTriple},
    types::{BasicTypeEnum, IntType, VoidType},
    values::{BasicValueEnum, FunctionValue, IntValue},
};
use peg::{error::ParseError, str::LineCol};
use std::{cell::RefCell, collections::HashMap, path::Path, process::Command, rc::Rc};

use crate::{
    ast::{
        FunctionDecl, Location, ProperStructDecl, RawStructDecl, TopLevelDecl, TopLevelDeclaration,
    },
    builders::{
        func::FunctionBuilder,
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
    pub path: String,
    pub content: String,
}

impl Input {
    pub fn from_string(content: &str) -> Self {
        Self {
            path: String::from("<buffer>"),
            content: content.to_string(),
        }
    }

    pub fn from_file(path: &Path) -> Self {
        Self {
            path: path.to_str().unwrap().to_string(),
            content: std::fs::read_to_string(path).unwrap(),
        }
    }
}

#[derive(Clone, Default)]
pub struct CompilerOptions {
    pub warn_as_err: bool,
    pub instrument_refcount: bool,
    pub link_extras: Vec<String>,
}

#[derive(Clone, Copy)]
pub struct BuiltinTypes<'a> {
    pub bool: IntType<'a>,
    pub byte: IntType<'a>,
    pub int32: IntType<'a>,
    pub int64: IntType<'a>,
    pub void: VoidType<'a>,
}

impl<'a> BuiltinTypes<'a> {
    pub fn new(c: &'a Context) -> Self {
        Self {
            bool: c.bool_type(),
            byte: c.i8_type(),
            int32: c.i32_type(),
            int64: c.i64_type(),
            void: c.void_type(),
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
}

#[derive(Clone)]
pub struct CompilerCore<'a> {
    pub context: &'a Context,
    pub refcnt: Refcounting<'a>,
    pub module: Rc<Module<'a>>,
    pub source: Input,
    pub options: CompilerOptions,
    pub funcs: MutableOf<HashMap<String, (FunctionDecl, FunctionValue<'a>)>>,
    pub types: MutableOf<HashMap<String, BasicTypeEnum<'a>>>,
    pub structs: MutableOf<HashMap<String, Structure<'a>>>,
    pub diagnostics: MutableOf<Vec<CompilerDiagnostic>>,
    pub builtins: BuiltinTypes<'a>,
    pub globals: Scope<'a>,
}

impl<'a> CompilerCore<'a> {
    pub fn new(
        context: &'a Context,
        triple: &str,
        src: &Input,
        options: CompilerOptions,
    ) -> CompilerCore<'a> {
        let triple = TargetTriple::create(triple);
        let module = Rc::new(context.create_module(""));
        module.set_triple(&triple);
        CompilerCore::fill_globals(&module, context);
        let refcnt = CompilerCore::fill_refcounting(&module, context, &options);
        let new = Self {
            context,
            refcnt,
            module,
            source: src.clone(),
            options,
            funcs: Rc::new(RefCell::new(HashMap::new())),
            types: Rc::new(RefCell::new(HashMap::new())),
            structs: Rc::new(RefCell::new(HashMap::new())),
            diagnostics: Rc::new(RefCell::new(Vec::new())),
            builtins: BuiltinTypes::new(context),
            globals: ScopeObject::root(),
        };
        new.fill_default_types();
        new
    }

    fn fill_default_types(&self) {
        use BasicTypeEnum::*;

        let mut types = self.types.borrow_mut();
        types.insert(String::from("byte"), IntType(self.builtins.byte));
        types.insert(String::from("int64"), IntType(self.builtins.int64));
        types.insert(String::from("int32"), IntType(self.builtins.int32));
        types.insert(String::from("bool"), IntType(self.builtins.bool));
    }

    fn fill_globals(m: &Module<'a>, c: &'a Context) {
        let bt = c.bool_type();
        let i64 = c.i64_type();
        let void = c.void_type();

        let itstrue = BasicValueEnum::IntValue(bt.const_int(1, false));
        let itsfalse = BasicValueEnum::IntValue(bt.const_int(0, false));

        m.add_global(bt, Default::default(), "true")
            .set_initializer(&itstrue);
        m.add_global(bt, Default::default(), "false")
            .set_initializer(&itsfalse);

        let freed_objects = BasicValueEnum::IntValue(i64.const_int(0, false));
        m.add_global(i64, Default::default(), "g_FreedObjects")
            .set_initializer(&freed_objects);

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
            TopLevelDecl::ExternFunction(fd) => {
                if fd.name.starts_with("__") {
                    self.error(CompilerError::new(
                        fd.loc,
                        Error::ReservedIdentifier(fd.name.clone()),
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
                            fb.declare(&fd.decl, false);
                        }
                        crate::ast::TopLevelDecl::ExternFunction(fd) => {
                            let fb = FunctionBuilder::new(self.clone());
                            fb.declare(fd, true);
                        }
                        crate::ast::TopLevelDecl::Structure(sd) => {
                            let ty = TypeBuilder::new(self.clone());
                            if let Some(psd) = self.fixup_struct_decl(sd) {
                                if ty.build_structure(&psd).is_none() {
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
                            if ty.alias(&ad.name, &ad.ty).is_none() {
                                self.error(CompilerError::new(ad.loc, Error::InvalidExpression));
                            }
                        }
                        crate::ast::TopLevelDecl::Implementation(id) => {
                            let ty = TypeBuilder::new(self.clone());
                            if let Some(struct_info) = self.structs.borrow().get(&id.name) {
                                ty.build_impl(struct_info, id);
                            } else {
                                self.error(CompilerError::new(
                                    id.loc,
                                    Error::TypeNotFound(crate::ast::TypeDescriptor::Name(
                                        id.name.clone(),
                                    )),
                                ));
                            }
                        }
                        crate::ast::TopLevelDecl::Variable(vd) => {
                            if vd.val.is_some() {
                                self.error(CompilerError::new(
                                    tld.loc,
                                    Error::InternalError(String::from(
                                        "globals cannot be initialized",
                                    )),
                                ));
                            } else if !vd.rw {
                                self.error(CompilerError::new(
                                    tld.loc,
                                    Error::InternalError(String::from(
                                        "globals cannot be read-only",
                                    )),
                                ));
                            } else if vd.ty.is_none() {
                                self.error(CompilerError::new(
                                    tld.loc,
                                    Error::InternalError(String::from(
                                        "globals must be explicitly typed",
                                    )),
                                ));
                            } else {
                                let tb = TypeBuilder::new(self.clone());
                                if let Some(var_type) =
                                    tb.llvm_type_by_descriptor(vd.ty.as_ref().unwrap())
                                {
                                    let global = self.module.add_global(
                                        var_type,
                                        Default::default(),
                                        &vd.name,
                                    );
                                    global.set_initializer(&TypeBuilder::zero_for_type(var_type));
                                    let vi = VarInfo::new(
                                        tld.loc,
                                        vd.name.clone(),
                                        global.as_pointer_value(),
                                        true,
                                    );
                                    self.globals.insert_variable(&vd.name, vi, true);
                                } else {
                                    self.error(CompilerError::new(
                                        tld.loc,
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
                            fb.build(fd);
                        }
                        crate::ast::TopLevelDecl::ExternFunction(..) => {}
                        crate::ast::TopLevelDecl::Structure(..) => {}
                        crate::ast::TopLevelDecl::Alias(..) => {}
                        crate::ast::TopLevelDecl::Implementation(..) => {}
                        crate::ast::TopLevelDecl::Variable(..) => {}
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
        Target::initialize_all(&Default::default());
        if let Ok(target) = Target::from_triple(&self.module.get_triple()) {
            if let Some(tm) = target.create_target_machine(
                &self.module.get_triple(),
                Default::default(),
                Default::default(),
                Default::default(),
                inkwell::targets::RelocMode::Default,
                inkwell::targets::CodeModel::Default,
            ) {
                let _ = tm.write_to_file(&self.module, inkwell::targets::FileType::Assembly, out);
                return;
            }
        }

        panic!("unable to create a target");
    }

    fn dump_to_obj(&self, out: &Path) {
        Target::initialize_all(&Default::default());
        if let Ok(target) = Target::from_triple(&self.module.get_triple()) {
            if let Some(tm) = target.create_target_machine(
                &self.module.get_triple(),
                Default::default(),
                Default::default(),
                Default::default(),
                inkwell::targets::RelocMode::DynamicNoPic,
                inkwell::targets::CodeModel::Default,
            ) {
                let _ = tm.write_to_file(&self.module, inkwell::targets::FileType::Object, out);
                return;
            }
        }

        panic!("unable to create a target");
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

    pub fn dump(&self, dest: &str) {
        let path = Path::new(dest);
        let ext = path.extension().map(|osstr| osstr.to_str().unwrap());
        match ext {
            Some("ir") => self.dump_to_ir(path),
            Some("ll") => self.dump_to_bc(path),
            Some("asm") => self.dump_to_asm(path),
            Some("obj") => self.dump_to_obj(path),
            _ => self.dump_to_binary(path),
        }
    }

    pub fn add_function(&self, fd: &FunctionDecl, fv: FunctionValue<'a>) {
        self.funcs
            .borrow_mut()
            .insert(fd.name.clone(), (fd.clone(), fv));
    }

    pub fn add_struct(&self, sd: &Structure<'a>) {
        self.structs
            .borrow_mut()
            .insert(sd.decl.name.clone(), sd.clone());
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
        let file_id = files.add(&self.source.path, &self.source.content);
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

        let file_id = files.add(&self.source.path, &self.source.content);

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

        let file_id = files.add(&self.source.path, &self.source.content);

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
