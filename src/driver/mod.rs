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

pub mod diags;

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    process::Command,
};

use inkwell::context::Context;
use rand::Rng;
use tempfile::NamedTempFile;

use crate::iw::{CompilerCore, CompilerOptions, Input};

pub struct DriverOptions {
    pub inputs: Vec<PathBuf>,
    pub output: PathBuf,
    pub libraries: Vec<String>,
    pub clang_options: Vec<String>,
}

fn is_cpm_source(p: &Path) -> bool {
    if let Some(ext) = p.extension() {
        matches!(ext.to_str().unwrap(), "cpm")
    } else {
        false
    }
}

pub type CompilerDiagnostics = HashMap<String, String>;

pub struct CompilationResult<TSuccess, TFailure> {
    pub result: Result<TSuccess, TFailure>,
    pub diagnostics: CompilerDiagnostics,
}

impl<TSuccess, TFailure> CompilationResult<TSuccess, TFailure> {
    pub fn ok<T: Into<TSuccess>>(s: T) -> Self {
        Self {
            result: Ok(s.into()),
            diagnostics: Default::default(),
        }
    }

    pub fn is_ok(&self) -> bool {
        matches!(self.result, Ok(..))
    }

    pub fn err<T: Into<TFailure>>(f: T) -> Self {
        Self {
            result: Err(f.into()),
            diagnostics: Default::default(),
        }
    }

    pub fn into_ok<T: Into<TSuccess>>(&mut self, s: T) -> &mut Self {
        self.result = Ok(s.into());

        self
    }

    pub fn into_err<T: Into<TFailure>>(&mut self, f: T) -> &mut Self {
        self.result = Err(f.into());

        self
    }

    pub fn set_diagnostics(&mut self, diags: HashMap<String, String>) -> &mut Self {
        self.diagnostics = diags;

        self
    }

    pub fn add_diagnostics(&mut self, file: &Path, diags: &str) -> &mut Self {
        self.diagnostics
            .insert(file.to_str().unwrap().to_owned(), diags.to_owned());

        self
    }
}

fn run_compiler_machinery<'a>(
    src: &Path,
    llvm: &'a Context,
    options: &CompilerOptions,
) -> (bool, CompilerCore<'a>) {
    let input = Input::from_file(src);
    let iwell = CompilerCore::new(llvm, &input, options.clone());
    let ok = iwell.compile();
    iwell.diagnostics.borrow().display_diagnostics();

    if ok {
        if options.optimize {
            iwell.run_passes();
        }
        if options.dump_ir_text {
            iwell.module.print_to_stderr();
        }
        if options.dump_bom {
            let mut bom_path = PathBuf::from(src);
            bom_path.set_extension("bom");
            iwell.dump_bom(bom_path.as_path());
        }
        (true, iwell)
    } else {
        (false, iwell)
    }
}

pub fn run_multi_jit(
    sources: &[PathBuf],
    options: &CompilerOptions,
) -> CompilationResult<u32, String> {
    let mut rng = rand::thread_rng();
    let n: u64 = rng.gen();
    let n = format!("jit_{n}");

    let mut aout_bld_path = tempfile::Builder::new();
    aout_bld_path.prefix(&n).suffix(".out");
    let aout_tmp_path = aout_bld_path.tempfile().expect("<io error>");
    let aout_path_buf = aout_tmp_path
        .path()
        .to_path_buf()
        .canonicalize()
        .expect("<io error>");
    let _ = aout_tmp_path.close();

    let ret = run_multi_jit_impl(sources, &aout_path_buf, options);
    let _ = std::fs::remove_file(aout_path_buf);
    ret
}

fn run_multi_jit_impl(
    sources: &[PathBuf],
    target: &PathBuf,
    options: &CompilerOptions,
) -> CompilationResult<u32, String> {
    let compile_result = build_aout(sources, target, options.clone());
    match compile_result.result {
        Ok(_) => {
            let mut cmd = Command::new(target);
            let child = cmd.spawn();
            match child {
                Ok(mut proc) => {
                    let exit = proc.wait();
                    match exit {
                        Ok(ec) => {
                            let ec = ec.code().unwrap() as u32;
                            let mut cr = CompilationResult::<u32, String>::ok(ec);
                            cr.set_diagnostics(compile_result.diagnostics);
                            cr
                        }
                        Err(err) => {
                            let err = format!("{err}");
                            let mut cr = CompilationResult::<u32, String>::err(err);
                            cr.set_diagnostics(compile_result.diagnostics);
                            cr
                        }
                    }
                }
                Err(err) => {
                    let err = format!("{err}");
                    let mut cr = CompilationResult::<u32, String>::err(err);
                    cr.set_diagnostics(compile_result.diagnostics);
                    cr
                }
            }
        }
        Err(err) => {
            let mut cr = CompilationResult::<u32, String>::err(err);
            cr.set_diagnostics(compile_result.diagnostics);
            cr
        }
    }
}

const REFCOUNT_SOURCE_CODE: &str = include_str!("../lib/refcount.c");

pub fn build_aout(
    sources: &[PathBuf],
    target: &Path,
    options: CompilerOptions,
) -> CompilationResult<(), String> {
    use std::io::Write;

    let mut rst = CompilationResult::ok(());

    let mut tempfiles: Vec<NamedTempFile> = vec![];
    let mut object_files: Vec<PathBuf> = vec![];
    for src in sources {
        if is_cpm_source(src) {
            let llvm = Context::create();
            match run_compiler_machinery(src.as_path(), &llvm, &options) {
                (true, iwell) => {
                    let mut ntf_builder = tempfile::Builder::new();
                    ntf_builder.suffix(".obj");
                    let tmp_file = ntf_builder.tempfile().expect("valid output file");
                    object_files.push(tmp_file.path().to_path_buf());
                    iwell.dump(tmp_file.path());
                    tempfiles.push(tmp_file);
                    rst.add_diagnostics(
                        src.as_path(),
                        &iwell.diagnostics.borrow().diagnostics_to_string(),
                    );
                }
                (false, iwell) => {
                    rst.add_diagnostics(
                        src.as_path(),
                        &iwell.diagnostics.borrow().diagnostics_to_string(),
                    );
                    rst.into_err("compilation error");
                    return rst;
                }
            };
        } else {
            object_files.push(src.clone());
        }
    }

    let refcount_tmp_file = tempfile::Builder::new()
        .suffix(".c")
        .tempfile()
        .expect("<io error>");
    write!(refcount_tmp_file.as_file(), "{}", REFCOUNT_SOURCE_CODE).expect("<io error>");
    object_files.push(refcount_tmp_file.path().to_path_buf());

    let mut clang = Command::new("clang");
    for objf in &object_files {
        clang.arg(objf.as_os_str().to_str().unwrap());
    }
    for le in &options.link_extras {
        clang.arg(format!("-l{le}"));
    }
    clang
        .arg("-lm")
        .arg("-fPIC")
        .arg("-o")
        .arg(target.as_os_str().to_str().unwrap());

    if options.instrument_refcount {
        clang.arg("-DINSTRUMENT_REFCOUNT");
    }

    let process = clang.spawn();
    if let Ok(mut child) = process {
        match child.wait() {
            Ok(_) => {}
            Err(err) => {
                rst.into_err(format!("linker execution failed: {err}"));
            }
        }
    } else {
        rst.into_err("unable to spawn system compiler; consider installing clang");
    }

    rst
}

pub fn build_objects(sources: &[PathBuf], options: CompilerOptions) -> Result<(), String> {
    for src in sources {
        if is_cpm_source(src) {
            let llvm = Context::create();
            match run_compiler_machinery(src.as_path(), &llvm, &options) {
                (true, iwell) => {
                    let mut dst = src.clone();
                    dst.set_extension("obj");
                    iwell.dump(dst.as_path());
                }
                (false, iwell) => {
                    return Err(iwell.diagnostics.borrow().diagnostics_to_string());
                }
            };
        }
    }

    Ok(())
}
