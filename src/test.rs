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
    RuntimeJit(String),
}

impl Display for TestFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
    use std::{io::ErrorKind, path::PathBuf, process::Stdio};

    use crate::iw::CompilerOptions;

    #[derive(Clone, Debug)]
    struct RuntimeExit {
        pub ec: Option<i32>,
        pub stdout: String,
        pub stderr: String,
    }

    #[derive(Clone, Debug)]
    enum TestOutcome {
        CompilationFailure,
        RuntimeError(ErrorKind),
        RuntimeComplete(RuntimeExit),
    }

    #[derive(Clone, Debug)]
    struct DriverTestResult {
        pub diags: crate::driver::CompilerDiagnostics,
        pub outcome: TestOutcome,
    }

    impl DriverTestResult {
        pub fn new(diags: &crate::driver::CompilerDiagnostics, outcome: TestOutcome) -> Self {
            Self {
                diags: diags.clone(),
                outcome,
            }
        }
    }

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
    ) -> DriverTestResult {
        let cmplr = crate::driver::build_aout(sources, target, options.clone());
        if let Err(_) = cmplr.result {
            return DriverTestResult::new(&cmplr.diagnostics, TestOutcome::CompilationFailure);
        }
        let mut cmd = std::process::Command::new(target);
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
        match cmd.spawn() {
            Ok(child) => {
                let result = child.wait_with_output();
                match result {
                    Ok(output) => {
                        let stdout = String::from_utf8(output.stdout).unwrap();
                        let stderr = String::from_utf8(output.stderr).unwrap();
                        let ec = output.status.code();
                        let re = RuntimeExit { ec, stdout, stderr };
                        return DriverTestResult::new(
                            &cmplr.diagnostics,
                            TestOutcome::RuntimeComplete(re),
                        );
                    }
                    Err(err) => {
                        return DriverTestResult::new(
                            &cmplr.diagnostics,
                            TestOutcome::RuntimeError(err.kind()),
                        );
                    }
                }
            }
            Err(err) => {
                return DriverTestResult::new(
                    &cmplr.diagnostics,
                    TestOutcome::RuntimeError(err.kind()),
                );
            }
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

    fn match_diags(expected_diags: &[String], actual_result: &DriverTestResult, matching: bool) {
        for diag in expected_diags {
            assert!(find_string_in_map(diag, &actual_result.diags) == matching);
        }
    }

    fn match_stdout_stderr(
        expected_stdout: &[String],
        expected_stderr: &[String],
        actual_result: &RuntimeExit,
        matching: bool,
    ) {
        for stdout in expected_stdout {
            assert!(actual_result.stdout.contains(stdout) == matching);
        }
        for stderr in expected_stderr {
            assert!(actual_result.stderr.contains(stderr) == matching);
        }
    }

    fn expect_driver_pass(
        sources: &[PathBuf],
        target: &PathBuf,
        options: &CompilerOptions,
        diags_match: &Option<Vec<String>>,
        stdout_match: &Option<Vec<String>>,
        stderr_match: &Option<Vec<String>>,
    ) {
        let run_result = compile_run_temp(sources, target, options);
        if let Some(expected_diags) = diags_match {
            match_diags(expected_diags, &run_result, true);
        }
        match run_result.outcome {
            TestOutcome::CompilationFailure | TestOutcome::RuntimeError(..) => {
                eprintln!("test failure: {:#?}", run_result.outcome);
                assert!(false);
            }
            TestOutcome::RuntimeComplete(out) => {
                assert!(out.ec.is_some());
                assert!(out.ec.unwrap() == 0);

                match_stdout_stderr(
                    if stdout_match.is_some() {
                        stdout_match.as_ref().unwrap()
                    } else {
                        &[]
                    },
                    if stderr_match.is_some() {
                        stderr_match.as_ref().unwrap()
                    } else {
                        &[]
                    },
                    &out,
                    true,
                );
            }
        }
    }

    #[allow(dead_code)]
    fn expect_driver_fail(
        sources: &[PathBuf],
        target: &PathBuf,
        options: &CompilerOptions,
        diags_match: &Option<Vec<String>>,
        stdout_match: &Option<Vec<String>>,
        stderr_match: &Option<Vec<String>>,
    ) {
        let run_result = compile_run_temp(sources, target, options);
        if let Some(expected_diags) = diags_match {
            match_diags(expected_diags, &run_result, true);
        }
        match run_result.outcome {
            TestOutcome::CompilationFailure | TestOutcome::RuntimeError(..) => {}
            TestOutcome::RuntimeComplete(out) => {
                assert!(out.ec.is_none() || out.ec.unwrap() != 0);

                match_stdout_stderr(
                    if stdout_match.is_some() {
                        stdout_match.as_ref().unwrap()
                    } else {
                        &[]
                    },
                    if stderr_match.is_some() {
                        stderr_match.as_ref().unwrap()
                    } else {
                        &[]
                    },
                    &out,
                    true,
                );
            }
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
                assert_eq!(result.unwrap(), 0);
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
