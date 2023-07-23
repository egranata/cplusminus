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

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use inkwell::{context::Context, execution_engine::JitFunction};
use tempfile::NamedTempFile;

use crate::{
    iw::{CompilerCore, CompilerOptions, Input},
    jit,
};

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

fn run_compiler_machinery<'a>(
    src: &Path,
    llvm: &'a Context,
    options: &CompilerOptions,
) -> Result<CompilerCore<'a>, ()> {
    let input = Input::from_file(src);
    let iwell = CompilerCore::new(llvm, &input, options.clone());
    let ok = iwell.compile();
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
        Ok(iwell)
    } else {
        iwell.display_diagnostics();
        Err(())
    }
}

pub fn run_jit(src: &Path, options: &CompilerOptions) -> Result<u64, String> {
    let llvm = Context::create();
    let rst: Result<u64, String>;
    match run_compiler_machinery(src, &llvm, options) {
        Ok(iwell) => {
            type MainFunc = unsafe extern "C" fn() -> u64;
            let main: Option<JitFunction<MainFunc>> =
                jit::get_runnable_function(&iwell, "main", options.optimize);
            if let Some(main) = main {
                let ret = unsafe { main.call() };
                rst = Ok(ret);
            } else {
                rst = Err(String::from("main not found"));
            }
        }
        Err(..) => {
            rst = Err(String::from("compilation error"));
        }
    };
    rst
}

pub fn build_aout(sources: &[PathBuf], target: PathBuf, options: CompilerOptions) {
    let mut tempfiles: Vec<NamedTempFile> = vec![];
    let mut object_files: Vec<PathBuf> = vec![];
    for src in sources {
        if is_cpm_source(src) {
            let llvm = Context::create();
            match run_compiler_machinery(src.as_path(), &llvm, &options) {
                Ok(iwell) => {
                    let mut ntf_builder = tempfile::Builder::new();
                    ntf_builder.suffix(".obj");
                    let tmp_file = ntf_builder.tempfile().expect("valid output file");
                    object_files.push(tmp_file.path().to_path_buf());
                    iwell.dump(tmp_file.path());
                    tempfiles.push(tmp_file);
                }
                Err(..) => return,
            };
        } else {
            object_files.push(src.clone());
        }
    }

    let mut clang = Command::new("clang");
    for objf in &object_files {
        clang.arg(objf.as_os_str().to_str().unwrap());
    }
    for le in &options.link_extras {
        clang.arg(format!("-l{le}"));
    }
    clang
        .arg("-fPIC")
        .arg("-o")
        .arg(target.as_os_str().to_str().unwrap());

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
}

pub fn build_objects(sources: &[PathBuf], options: CompilerOptions) {
    for src in sources {
        if is_cpm_source(src) {
            let llvm = Context::create();
            match run_compiler_machinery(src.as_path(), &llvm, &options) {
                Ok(iwell) => {
                    let mut dst = src.clone();
                    dst.set_extension("obj");
                    iwell.dump(dst.as_path());
                }
                Err(..) => return,
            };
        }
    }
}
