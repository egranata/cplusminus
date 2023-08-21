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
    types::BasicTypeEnum,
    values::{BasicValueEnum, FunctionValue, GlobalValue},
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
    ast::{
        ProperStructDecl, RawStructDecl, TokenLocation, TokenSpan, TopLevelDecl,
        TopLevelDeclaration, TypeDescriptor,
    },
    bom::{
        alias::AliasBomEntry, function::FunctionBomEntry, module::BillOfMaterials,
        strct::StructBomEntry, variable::VariableBomEntry,
    },
    builders::{
        func::{FunctionBuilder, FunctionBuilderOptions},
        refcount::Refcounting,
        scope::{Scope, ScopeObject, VarInfo},
        ty::TypeBuilder,
    },
    codegen::{builtins::BuiltinTypes, metadata::Metadata},
    err::{CompilerError, CompilerWarning, Error, Warning},
    parser::cpm::source_file,
};

use crate::codegen::{structure::Structure, MutableOf};

use codespan_reporting::files::{Files, SimpleFile};

#[derive(Clone)]
pub struct Input {
    pub path: PathBuf,
    pub content: String,
    pub diag_file: SimpleFile<String, String>,
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
        let content = content.to_owned();
        Self {
            path: PathBuf::new(),
            content: content.clone(),
            diag_file: SimpleFile::new(String::from("<buffer>"), content),
        }
    }

    pub fn from_file(path: &Path) -> Self {
        let path = path.to_path_buf();
        let content = std::fs::read_to_string(&path).unwrap();

        Self {
            path: path.clone(),
            content: content.clone(),
            diag_file: SimpleFile::new(path.to_str().unwrap().to_owned(), content),
        }
    }

    pub fn path_to_string(&self) -> String {
        if self.path.exists() {
            self.path.to_str().unwrap().to_owned()
        } else {
            String::from("<unknown buffer>")
        }
    }

    pub fn index_to_location(&self, idx: usize) -> TokenLocation {
        let loc = self.diag_file.location((), idx).unwrap();
        TokenLocation {
            line: loc.line_number,
            column: loc.column_number,
        }
    }
}

#[derive(Clone, Debug, Copy, Eq, PartialEq)]
pub enum OutputMode {
    Jit,
    Binary,
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
    pub debug: bool,
    pub out: OutputMode,
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
            debug: false,
            out: OutputMode::Jit,
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

#[derive(Clone)]
pub struct CompilerCore<'a> {
    pub context: &'a Context,
    pub refcnt: Refcounting<'a>,
    pub metadata: Metadata<'a>,
    pub module: Rc<Module<'a>>,
    pub target: Rc<Target>,
    pub machine: Rc<TargetMachine>,
    pub source: Input,
    pub options: CompilerOptions,
    pub structs: MutableOf<HashMap<String, Structure<'a>>>,
    pub diagnostics: MutableOf<crate::driver::diags::Diagnostics>,
    pub builtins: BuiltinTypes<'a>,
    pub globals: Scope<'a>,
    pub bom: MutableOf<BillOfMaterials>,
}

impl<'a> CompilerCore<'a> {
    pub fn new(context: &'a Context, src: &Input, options: CompilerOptions) -> CompilerCore<'a> {
        let triple = TargetTriple::create(&options.triple);
        let module = Rc::new(context.create_module(""));
        module.set_triple(&triple);
        let warn_as_err = options.warn_as_err;

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
        let metadata = Metadata::build(context);
        let new = Self {
            context,
            refcnt,
            metadata,
            module,
            target: Rc::from(target),
            machine: Rc::from(tm),
            source: src.clone(),
            options,
            structs: Rc::new(RefCell::new(HashMap::new())),
            diagnostics: crate::driver::diags::Diagnostics::new(warn_as_err, src),
            builtins: BuiltinTypes::new(context),
            globals: ScopeObject::root(),
            bom: Default::default(),
        };
        new.fill_default_types();
        new.forbid_32bit_targets();
        new.no_rc_instrument_for_jit();
        new
    }

    fn forbid_32bit_targets(&self) {
        if self.machine.get_target_data().get_pointer_byte_size(None) != 8 {
            self.diagnostics
                .borrow_mut()
                .error(CompilerError::unbound(Error::ThirtyTwoBitUnsupported));
        }
    }

    fn no_rc_instrument_for_jit(&self) {
        if self.options.instrument_refcount && self.options.out == OutputMode::Jit {
            self.diagnostics
                .borrow_mut()
                .warning(CompilerWarning::unbound(
                    Warning::CannotInstrumentJitRefcount,
                ));
        }
    }

    fn fill_default_types(&self) {
        for (n, t) in self.builtins.builtin_types_map().iter() {
            self.globals.insert_alias(n.as_str(), *t, true);
        }
    }

    pub fn make_global(
        m: &Module<'a>,
        name: &str,
        ty: BasicTypeEnum<'a>,
        val: Option<BasicValueEnum<'a>>,
        lnk: Linkage,
        constant: bool,
    ) -> GlobalValue<'a> {
        let global = m.add_global(ty, Default::default(), name);
        if let Some(val) = val {
            global.set_initializer(&val);
            global.set_constant(constant);
        }
        global.set_linkage(lnk);
        global
    }

    fn fill_globals(m: &Module<'a>, c: &'a Context) {
        let bt = c.bool_type();
        let void = c.void_type();

        let itstrue = BasicValueEnum::IntValue(bt.const_int(1, false));
        let itsfalse = BasicValueEnum::IntValue(bt.const_int(0, false));

        CompilerCore::make_global(
            m,
            "true",
            itstrue.get_type(),
            Some(itstrue),
            Linkage::Internal,
            true,
        );
        CompilerCore::make_global(
            m,
            "false",
            itsfalse.get_type(),
            Some(itsfalse),
            Linkage::Internal,
            true,
        );

        let trap_type = void.fn_type(&[], false);
        m.add_function("llvm.trap", trap_type, Some(Linkage::Internal));
    }

    fn fill_refcounting(
        m: &Module<'a>,
        c: &'a Context,
        options: &CompilerOptions,
    ) -> Refcounting<'a> {
        let i64 = c.i64_type();

        CompilerCore::make_global(
            m,
            "g_FreedObjects",
            BasicTypeEnum::IntType(i64),
            if options.out == OutputMode::Jit {
                Some(BasicValueEnum::IntValue(i64.const_zero()))
            } else {
                None
            },
            if options.out == OutputMode::Jit {
                Linkage::Internal
            } else {
                Linkage::External
            },
            false,
        );

        crate::builders::refcount::build_refcount_apis(m, c)
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
            export: raw.export,
        };

        for entry in &raw.entries {
            match entry {
                crate::ast::StructEntryDecl::Field(field) => proper.fields.push(field.clone()),
                crate::ast::StructEntryDecl::Init(init) => {
                    if proper.init.is_some() {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
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
                        self.diagnostics.borrow_mut().error(CompilerError::new(
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

    fn check_ast_decl(&self, tld: &TopLevelDeclaration) -> bool {
        let allowed = tld.name().map_or(true, |name| !name.starts_with("__"));
        if !allowed {
            self.diagnostics.borrow_mut().error(CompilerError::new(
                tld.loc,
                Error::ReservedIdentifier(tld.name().unwrap()),
            ));
            false
        } else {
            if let TopLevelDecl::Structure(st) = &tld.payload {
                for entry in &st.entries {
                    if let crate::ast::StructEntryDecl::Field(f) = entry {
                        if f.name.starts_with("__") {
                            self.diagnostics.borrow_mut().error(CompilerError::new(
                                f.loc,
                                Error::ReservedIdentifier(f.name.clone()),
                            ));
                            return false;
                        }
                    }
                }
            }

            allowed
        }
    }

    fn import(&self, id: &crate::ast::ImportDecl, bom: &BillOfMaterials) {
        for sd in &bom.structs {
            if let Some(ty) = sd.import(self, &self.globals) {
                self.metadata.import_metadata_for_type(self, ty);
            } else {
                self.diagnostics.borrow_mut().error(CompilerError::new(
                    id.loc,
                    Error::ImportFailed(sd.name.clone()),
                ));
            }
        }

        for ta in &bom.aliases {
            if ta.import(self, &self.globals).is_none() {
                self.diagnostics.borrow_mut().error(CompilerError::new(
                    id.loc,
                    Error::ImportFailed(ta.user_facing_name.clone()),
                ));
            }
        }

        for gv in &bom.variables {
            if gv.import(self, &self.globals).is_none() {
                self.diagnostics.borrow_mut().error(CompilerError::new(
                    id.loc,
                    Error::ImportFailed(gv.user_facing_name.clone()),
                ));
            }
        }

        for ef in &bom.functions {
            if ef.import(self, &self.globals).is_none() {
                self.diagnostics.borrow_mut().error(CompilerError::new(
                    id.loc,
                    Error::ImportFailed(ef.user_facing_name.clone()),
                ));
            }
        }

        for il in &bom.impls {
            let tb = TypeBuilder::new(self.clone());
            let struct_descriptor = TypeDescriptor::Name(il.struct_name.clone());
            if let Some(bst) = tb.llvm_type_by_descriptor(&self.globals, &struct_descriptor) {
                if let Some(structure) = tb.is_val_or_ref_basic_type(bst) {
                    if let Some(sdef) = tb.struct_by_name(structure) {
                        if il.import(self, &sdef).is_none() {
                            self.diagnostics.borrow_mut().error(CompilerError::new(
                                id.loc,
                                Error::ImportFailed(format!("impl {}", struct_descriptor)),
                            ));
                        }
                    }
                }
            }
        }
    }

    fn sanitize_ast(&self, tlds: Vec<TopLevelDeclaration>) -> Vec<TopLevelDeclaration> {
        let mut ret: Vec<TopLevelDeclaration> = vec![];
        for tld in tlds {
            if self.check_ast_decl(&tld) {
                ret.push(tld);
            }
        }

        ret
    }

    fn declare_pass(&self, tlds: &[TopLevelDeclaration]) -> bool {
        for tld in tlds {
            let tb: TypeBuilder<'a> = TypeBuilder::new(self.clone());

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
                    if let Some(psd) = self.fixup_struct_decl(sd) {
                        if let Some(st) = tb.build_structure_from_decl(&self.globals, &psd) {
                            self.metadata.build_metadata_for_type(self, &tb, st);
                            if let Some(strct) = tb.struct_by_name(st) {
                                if psd.export {
                                    let bom_entry = StructBomEntry::new(&strct);
                                    self.bom.borrow_mut().structs.push(bom_entry);
                                }
                            }
                        } else {
                            self.diagnostics
                                .borrow_mut()
                                .error(CompilerError::new(sd.loc, Error::InvalidExpression));
                        }
                    } else {
                        self.diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(sd.loc, Error::InvalidExpression));
                    }
                }
                crate::ast::TopLevelDecl::Alias(ad) => {
                    if let Some(uty) = tb.alias(&self.globals, &ad.name, &ad.ty) {
                        if ad.export {
                            // we just generated this from a descriptor, assume roundtrip is safe
                            let utd = TypeBuilder::descriptor_by_llvm_type(uty).unwrap();
                            let bom_entry = AliasBomEntry::new(&ad.name, &utd);
                            self.bom.borrow_mut().aliases.push(bom_entry);
                        }
                    } else {
                        self.diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(ad.loc, Error::InvalidExpression));
                    }
                }
                crate::ast::TopLevelDecl::Implementation(id) => {
                    if let Some(ty) = tb.llvm_type_by_descriptor(&self.globals, &id.of) {
                        if let Some(sty) = tb.is_val_or_ref_basic_type(ty) {
                            if let Some(struct_info) = tb.struct_by_name(sty) {
                                tb.build_impl(&self.globals, &struct_info, id);
                            } else {
                                self.diagnostics.borrow_mut().error(CompilerError::new(
                                    id.loc,
                                    Error::TypeNotFound(id.of.clone()),
                                ));
                            }
                        } else {
                            self.diagnostics.borrow_mut().error(CompilerError::new(
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
                        self.import(id, &bom);
                    } else {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
                            tld.loc,
                            Error::InternalError(String::from("unable to find BOM")),
                        ));
                    }
                }
                crate::ast::TopLevelDecl::Variable(gvd) => {
                    let vd = &gvd.decl;
                    if vd.val.is_some() {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
                            gvd.loc,
                            Error::InternalError(String::from("globals cannot be initialized")),
                        ));
                    } else if !vd.rw {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
                            gvd.loc,
                            Error::InternalError(String::from("globals cannot be read-only")),
                        ));
                    } else if vd.ty.is_none() {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
                            gvd.loc,
                            Error::InternalError(String::from("globals must be explicitly typed")),
                        ));
                    } else if let Some(var_type) =
                        tb.llvm_type_by_descriptor(&self.globals, vd.ty.as_ref().unwrap())
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
                            false,
                        );

                        let vi =
                            VarInfo::new(tld.loc, vd.name.clone(), global.as_pointer_value(), true);
                        self.globals.insert_variable(&vd.name, vi, true);

                        if gvd.export {
                            let bom_entry = VariableBomEntry::new(
                                global.get_name().to_str().unwrap(),
                                vd.ty.as_ref().unwrap(),
                            );
                            self.bom.borrow_mut().variables.push(bom_entry);
                        }
                    } else {
                        self.diagnostics.borrow_mut().error(CompilerError::new(
                            gvd.loc,
                            Error::TypeNotFound(vd.ty.as_ref().unwrap().clone()),
                        ));
                    }
                }
            }
        }

        self.success()
    }

    fn define_pass(&self, tlds: &[TopLevelDeclaration]) -> bool {
        for tld in tlds {
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

        self.success()
    }

    fn compile_tlds(&self, tlds: &[TopLevelDeclaration]) -> bool {
        if self.declare_pass(tlds) {
            self.define_pass(tlds)
        } else {
            false
        }
    }

    pub fn compile(&self) -> bool {
        let parsed = self.parse();
        match parsed {
            Ok(tlds) => {
                let tlds = self.sanitize_ast(tlds);
                self.compile_tlds(&tlds)
            }
            Err(err) => {
                let loc = TokenSpan {
                    start: err.location.offset,
                    end: err.location.offset + 1,
                };
                self.diagnostics.borrow_mut().error(CompilerError::new(
                    loc,
                    Error::ParseError(err.expected.to_string()),
                ));
                false
            }
        }
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

    pub fn success(&self) -> bool {
        self.diagnostics.borrow().ok()
    }
}
