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

use std::fmt::Display;

#[derive(Clone, Debug)]
enum TestFailure {
    CompileFailure(crate::driver::CompilerDiagnostics),
    RuntimeNoSpawn(String),
    RuntimeNoExitCode,
    RuntimeJit(String),
}

impl Display for TestFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestFailure::CompileFailure(_) => write!(f, "compiler error"),
            TestFailure::RuntimeNoSpawn(err) => write!(f, "program execution failed: {err}"),
            TestFailure::RuntimeNoExitCode => write!(f, "program did not exit with a result"),
            TestFailure::RuntimeJit(err) => write!(f, "LLVM JIT error: {err}"),
        }
    }
}

struct FileToBeDropped {
    path: String,
}

impl Drop for FileToBeDropped {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

#[cfg(test)]
mod driver_tests {
    use std::path::PathBuf;

    use crate::iw::CompilerOptions;

    use super::TestFailure;

    fn remove_stale_files(dest: &PathBuf) {
        let container = dest.parent().unwrap().to_path_buf();
        let aout = container.clone().join("a.out");
        let _ = std::fs::remove_file(&aout);
        for path in glob::glob(&format!("{}", container.join("*.bom").display())).unwrap() {
            if let Ok(path) = path {
                let _ = std::fs::remove_file(&path);
            }
        }
    }

    fn compile_run_temp(
        sources: &[PathBuf],
        target: &PathBuf,
        options: &CompilerOptions,
    ) -> Result<(i32, crate::driver::CompilerDiagnostics), TestFailure> {
        let cmplr = crate::driver::build_aout(sources, target, options.clone());
        if let Err(_) = cmplr.result {
            return Err(TestFailure::CompileFailure(cmplr.diagnostics));
        }
        let mut cmd = std::process::Command::new(target);
        match cmd.spawn() {
            Ok(mut child) => match child.wait() {
                Ok(exit) => match exit.code() {
                    Some(code) => return Ok((code, cmplr.diagnostics)),
                    None => return Err(TestFailure::RuntimeNoExitCode),
                },
                Err(err) => {
                    return Err(TestFailure::RuntimeNoSpawn(err.to_string()));
                }
            },
            Err(err) => {
                return Err(TestFailure::RuntimeNoSpawn(err.to_string()));
            }
        }
    }

    fn expect_driver_pass(
        sources: &[PathBuf],
        target: &PathBuf,
        options: &CompilerOptions,
        diags: &Option<Vec<String>>,
    ) {
        let result = compile_run_temp(sources, target, options);
        if result.is_ok() {
            let (rc, compiler_diagnostics) = result.unwrap();
            assert!(rc == 0);
            if let Some(diags) = diags {
                for diag in diags {
                    assert!(find_string_in_map(&diag, &compiler_diagnostics));
                }
            }
        } else {
            eprintln!("test failure: {}", result.unwrap_err());
            assert!(false);
        }
    }

    fn find_string_in_map(msg: &str, diags: &crate::driver::CompilerDiagnostics) -> bool {
        for diag in diags.values() {
            if diag.contains(msg) {
                return true;
            }
        }

        return false;
    }

    #[allow(dead_code)]
    fn expect_driver_fail(
        sources: &[PathBuf],
        target: &PathBuf,
        options: &CompilerOptions,
        diags: &Option<Vec<String>>,
    ) {
        let result = compile_run_temp(sources, target, options);
        assert!(result.is_err());
        match result.unwrap_err() {
            TestFailure::CompileFailure(compiler_diagnostics) => {
                if let Some(diags) = diags {
                    for diag in diags {
                        assert!(find_string_in_map(&diag, &compiler_diagnostics));
                    }
                }
            }
            _ => {}
        }
    }

    include!(concat!(env!("OUT_DIR"), "/test_driverpass.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_driverfail.rs"));
}

#[cfg(test)]
mod jit_tests {
    use std::path::PathBuf;

    use crate::iw::CompilerOptions;

    use super::TestFailure;

    fn run_jit_source(program: &PathBuf, optimize: bool) -> Result<u32, TestFailure> {
        let compiler_options = if optimize {
            CompilerOptions::unoptimized()
        } else {
            CompilerOptions::optimized()
        };

        let sources: Vec<PathBuf> = vec![program.clone()];

        let result = crate::driver::run_multi_jit(&sources, &compiler_options);
        return match result.result {
            Ok(ret) => Ok(ret),
            Err(msg) => Err(TestFailure::RuntimeJit(msg)),
        };
    }

    fn expect_jit_pass(program: PathBuf) {
        for opt in &[false, true] {
            let result = run_jit_source(&program, *opt);
            if result.is_ok() {
                assert!(result.unwrap() == 0);
            } else {
                eprintln!("test failure: {}", result.unwrap_err());
                assert!(false);
            }
        }
    }

    fn expect_jit_fail(program: PathBuf) {
        for opt in &[false, true] {
            let result = run_jit_source(&program, *opt);
            assert!(result.is_err());
        }
    }

    include!(concat!(env!("OUT_DIR"), "/test_jitpass.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_jitfail.rs"));
}
