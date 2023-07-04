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
    CompileTime(Vec<crate::err::CompilerDiagnostic>),
    RuntimeNoMain,
    RuntimeNoSpawn(String),
    RuntimeNoExitCode,
}

impl Display for TestFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestFailure::CompileTime(_) => write!(f, "compilation failed"),
            TestFailure::RuntimeNoMain => write!(f, "main function not found"),
            TestFailure::RuntimeNoSpawn(err) => write!(f, "program execution failed: {err}"),
            TestFailure::RuntimeNoExitCode => write!(f, "program did not exit with a result"),
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
mod aout_tests {
    use crate::iw::{self, Input};
    use inkwell::context::Context;
    use rand::Rng;

    use super::{FileToBeDropped, TestFailure};

    fn compile_run_temp(program: &str, optimize: bool) -> Result<i32, TestFailure> {
        let mut rng = rand::thread_rng();
        let llvm = Context::create();
        let source = Input::from_string(program);
        let iwell =
            iw::CompilerCore::new(&llvm, "x86_64-pc-linux-gnu", &source, Default::default());
        if iwell.compile() {
            if optimize {
                iwell.run_passes();
            }
            let mut temp_dir = std::env::temp_dir();
            let n: u32 = rng.gen();
            temp_dir.push(format!("test{}.out", n));
            let temp_aout_path = FileToBeDropped {
                path: temp_dir.as_path().as_os_str().to_str().unwrap().to_string(),
            };
            iwell.dump(&temp_aout_path.path);
            println!("trying to run {}", &temp_aout_path.path);
            let mut cmd = std::process::Command::new(&temp_aout_path.path);
            match cmd.spawn() {
                Ok(mut child) => match child.wait() {
                    Ok(exit) => match exit.code() {
                        Some(code) => return Ok(code),
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
        } else {
            return Err(TestFailure::CompileTime(
                iwell.diagnostics.as_ref().borrow().clone(),
            ));
        }
    }

    fn expect_aout_pass(program: &str) {
        for opt in &[false, true] {
            let result = compile_run_temp(program, *opt);
            if result.is_ok() {
                assert!(result.unwrap() == 0);
            } else {
                eprintln!("test failure: {}", result.unwrap_err());
                assert!(false);
            }
        }
    }

    fn expect_aout_fail(program: &str) {
        for opt in &[false, true] {
            let result = compile_run_temp(program, *opt);
            assert!(result.is_err());
        }
    }

    include!(concat!(env!("OUT_DIR"), "/test_aoutpass.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_aoutfail.rs"));
}

#[cfg(test)]
mod jit_tests {
    use crate::{
        iw::{self, Input},
        jit,
    };
    use inkwell::{context::Context, execution_engine::JitFunction};

    use super::TestFailure;

    fn run_jit_source(program: &str, optimize: bool) -> Result<u64, TestFailure> {
        type MainFunc = unsafe extern "C" fn() -> u64;
        let llvm = Context::create();
        let source = Input::from_string(program);
        let iwell =
            iw::CompilerCore::new(&llvm, "x86_64-pc-linux-gnu", &source, Default::default());
        if iwell.compile() {
            if optimize {
                iwell.run_passes();
            }
            let main: Option<JitFunction<MainFunc>> =
                jit::get_runnable_function(&iwell, "main", false);
            if let Some(main) = main {
                return Ok(unsafe { main.call() });
            } else {
                return Err(TestFailure::RuntimeNoMain);
            }
        } else {
            return Err(TestFailure::CompileTime(
                iwell.diagnostics.as_ref().borrow().clone(),
            ));
        }
    }

    fn expect_jit_pass(program: &str) {
        for opt in &[false, true] {
            let result = run_jit_source(program, *opt);
            if result.is_ok() {
                assert!(result.unwrap() == 0);
            } else {
                eprintln!("test failure: {}", result.unwrap_err());
                assert!(false);
            }
        }
    }

    fn expect_jit_fail(program: &str) {
        for opt in &[false, true] {
            let result = run_jit_source(program, *opt);
            assert!(result.is_err());
        }
    }

    include!(concat!(env!("OUT_DIR"), "/test_jitpass.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_jitfail.rs"));
}

#[cfg(test)]
mod test {
    use inkwell::{context::Context, execution_engine::JitFunction};

    use crate::{
        err::{CompilerError, CompilerWarning},
        iw::{self, Input},
        jit,
    };

    fn helper_run_main_exit(program: &str) -> Option<u64> {
        type MainFunc = unsafe extern "C" fn() -> u64;
        let llvm = Context::create();
        let source = Input::from_string(program);
        let iwell =
            iw::CompilerCore::new(&llvm, "x86_64-pc-linux-gnu", &source, Default::default());
        if iwell.compile() {
            let main: Option<JitFunction<MainFunc>> =
                jit::get_runnable_function(&iwell, "main", false);
            if let Some(main) = main {
                return Some(unsafe { main.call() });
            } else {
                return None;
            }
        } else {
            return None;
        }
    }

    fn helper_compile_errors(program: &str) -> Vec<CompilerError> {
        let llvm = Context::create();
        let source = Input::from_string(program);
        let iwell =
            iw::CompilerCore::new(&llvm, "x86_64-pc-linux-gnu", &source, Default::default());
        iwell.compile();

        return iwell.errors();
    }

    fn helper_compile_warnings(program: &str) -> Vec<CompilerWarning> {
        let llvm = Context::create();
        let source = Input::from_string(program);
        let iwell =
            iw::CompilerCore::new(&llvm, "x86_64-pc-linux-gnu", &source, Default::default());
        iwell.compile();

        let x = iwell.errors();
        if x.len() > 0 {
            return vec![];
        };
        return iwell.warnings();
    }

    #[test]
    fn test_main_return() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_call_void_func() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func foo() {
    return;
}

func main() ret int64 {
    foo();
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_main_type_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func main() ret int24 {
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_valued_return_in_void() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo() {
    return 1;
}

func main() ret int64 {
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_void_return_in_valued() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo() ret byte {
    return;
}

func main() ret int64 {
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_var_decl_type_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
ref type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    let p: int32 = alloc pair;
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_ret_uses_hint() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int32 {
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_main_type_mismatch() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
val type foo {
    x: int32
}

func main() ret int32 {
    return alloc foo;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_var_assign_uses_hint() {
        assert_eq!(
            6,
            helper_run_main_exit(
                "
func main() ret int32 {
    var a = 5 as int32;
    a = 6;
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_arg_uses_hint() {
        assert_eq!(
            35,
            helper_run_main_exit(
                "
func foo(x: int32, y: int32) ret int32 {
    return x * y;
}

func main() ret int32 {
    return foo(3+4, 7-2);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_const_init_hinted() {
        assert_eq!(
            7,
            helper_run_main_exit(
                "
func main() ret int32 {
    let n: int32 = 7;
    return n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_write_to_let_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func main() ret int32 {
    let x = 12;
    x = 24;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_write_to_arg_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo(x: int64) ret int64 {
    x = 24;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_int64_addition() {
        assert_eq!(
            7,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 3 + 4;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_subtraction() {
        assert_eq!(
            120,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 123 - 3;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_negation() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    let a = 2;
    let a = -a;
    let n = a;
    let n = a + (-1);
    return n + 4;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_not() {
        assert_eq!(
            0xFFFFFFFFFFFFFFF8,
            helper_run_main_exit(
                "
func main() ret int64 {
    return !7;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_comments_everywhere() {
        assert_eq!(
            120,
            helper_run_main_exit(
                "
(* a comment *)
type pair {
    x: int64,
    y: int64
}

impl pair {
(* one more comment *)
    func copy() ret pair {
    (* lovely comment *)
        var q = alloc pair;
        q.x = self.x;
        q.y = self.y;
        return q;
    }
}

func foo() ret pair {
    var p = alloc pair;
    (* more comments *)
    (* this comment has spaces at the end    *)   
    p.x = 22;
    return p->copy();
}

func blah() ret int64 {
    let f = foo();
    return f.x;
}

(* this returns 120 *)
func main() ret int64 {
    (* here's the number 120 *)
    return 120;
}

"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_multiply() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 3 * 4;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_division() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 48 / 4;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_modulo() {
        assert_eq!(
            3,
            helper_run_main_exit(
                "
func main() ret int64 {
    return 23 % 5;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_and() {
        assert_eq!(
            0b100,
            helper_run_main_exit(
                "
func main() ret int64 {
    let n = b100110;
    let m = b011101;
    return (n && m);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_bool_and() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    assert true == (true && true);
    assert false == (true && false);
    assert false == (false && false);
    assert false == (false && true);
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_or() {
        assert_eq!(
            0b111110,
            helper_run_main_exit(
                "
func main() ret int64 {
    let n = b100110;
    let m = b011100;
    return (n || m);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_bool_or() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    assert true == (true || true);
    assert true == (true || false);
    assert false == (false || false);
    assert true == (false || true);
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_xor() {
        assert_eq!(
            0b111010,
            helper_run_main_exit(
                "
func main() ret int64 {
    let n = b100110;
    let m = b011100;
    return (n ^^ m);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_bool_xor() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    assert false == (true ^^ true);
    assert true == (true ^^ false);
    assert false == (false ^^ false);
    assert true == (false ^^ true);
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_bool_not() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    assert true == !false;
    assert false == !true;
    assert !!true;
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_gt() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 > 4) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 > 2) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 > 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_ge() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 >= 4) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 >= 2) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 >= 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_lt() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 < 4) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 < 2) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 < 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_le() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 <= 4) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 <= 2) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 <= 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_eq() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 == 3) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (2 == 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_int64_nq() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (3 != 3) as int64;
}
"
            )
            .unwrap()
        );

        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (2 != 3) as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_two_functions_defined() {
        assert_eq!(
            7,
            helper_run_main_exit(
                "
func main() ret int32 {
    return (3 + 4) as int32;
}

func foo(x: int64, y: int64) ret int64 {
    return x + y;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_simple_function_call() {
        assert_eq!(
            27,
            helper_run_main_exit(
                "
func foo(x: int32, y: int32, z: int32) ret int32 {
    return x + y * z;
}
        
func main() ret int32 {
    return foo(3,4,6);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_dup_arg_names() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo(x: int32, y: int32, x: int32) ret int32 {
    return x + y * z;
}
        
func main() ret int32 {
    return foo(3,4,6);
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_var_let_decl() {
        assert_eq!(
            8,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 5;
    let b = 3;
    a = a + b;
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_simple_function_call_fwd_decl() {
        assert_eq!(
            27,
            helper_run_main_exit(
                "
func main() ret int32 {
    return foo(3,4,6);
}
        
func foo(x: int32, y: int32, z: int32) ret int32 {
    return x + y * z;
}        
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_var_assignment() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 0;
    a = 12;
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_taken() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func main() ret int32 {
    var a = 1;
    if (12 > 3) {
        a = 12;
    };
    return a as int32;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_bitsize() {
        assert_eq!(
            102,
            helper_run_main_exit(
                "
func foo() ret int32 {
    return 230;
}

func main() ret int64 {
    let ch = foo();
    var n = 0;
    if (ch == 265) {
        n = 10;
    } else {
        n = 100;
    };

    if (265 == ch) {
        n = n + 1;
    } else {
        n = n + 2;
    };

    return n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_not_taken() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int32 {
    var a = 1;
    if (12 > 24) {
        a = 12;
    };
    return a as int32;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_taken_else() {
        assert_eq!(
            36,
            helper_run_main_exit(
                "
func main() ret int32 {
    var a = 1;
    if (12 > 34) {
        a = 12;
    } else {
        a = 36;
    };
    return a as int32;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_taken_elsif() {
        assert_eq!(
            22,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 1;
    if (12 > 34) {
        a = 12;
    } elsif (12 > 10) {
        a = 22;
    } else {
        a = 36;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_taken_one_of_elsif() {
        assert_eq!(
            22,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 1;
    if (12 > 34) {
        a = 12;
    } elsif (3 > 5) {
        a = 5;
    } elsif (12 > 10) {
        a = 22;
    } elsif (7 > 12) {
        a = 8;
    } elsif (12 > 7) {
        a = 6;
    } else {
        a = 36;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_return() {
        assert_eq!(
            22,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 1;
    if (12 > 34) {
        return 12;
    } elsif (3 > 5) {
        return 5;
    } elsif (12 > 10) {
        return 22;
    } elsif (7 > 12) {
        return 8;
    } elsif (12 > 7) {
        return 6;
    } else {
        a = 36;
        return a;
    };
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_true() {
        assert_eq!(
            13,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 1;
    var b = 1;
    if (true) {
        a = 12;
    };

    if (false) {
        b = 21;
    };
    
    return a + b;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_init_default_var() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = 1;
    var b: int64;
    return a + b;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_err_typeless_var() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func main() ret int64 {
    var x;
    return 12;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_err_default_let() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func main() ret int64 {
    let x: int64;
    return 12;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_define_ref_struct() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_define_val_struct() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
val type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_struct_access() {
        assert_eq!(
            8,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    let p = alloc pair;
    p.x = 3;
    p.y = 4;
    return p.x + p.y + 1;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_val_struct_access() {
        assert_eq!(
            8,
            helper_run_main_exit(
                "
val type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    let p = alloc pair;
    p.x = 3;
    p.y = 4;
    return p.x + p.y + 1;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_struct_access_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    var p = alloc pair;
    p.no = 3;
    p.such = 4;
    return p.x + p.field + 1;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_val_struct_access_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
val type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    var p = alloc pair;
    p.no = 3;
    p.such = 4;
    return p.x + p.field + 1;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_let_struct_write_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    let p = alloc pair;
    p.x = 3;
    p = alloc pair;
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_expr_statmt() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    3 + 4;
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_nested_struct_access() {
        assert_eq!(
            25,
            helper_run_main_exit(
                "
type counter {
    n: int64
}

type counters {
    c1: counter,
    c2: counter
}

impl counters {
    func init() ret int64 {
        self.c1 = alloc counter;
        self.c2 = alloc counter;
        return 0;
    }
}

func main() ret int64 {
    let cc = alloc counters;
    cc->init();
    cc.c1.n = 12;
    cc.c2.n = 13;
    return cc.c1.n + cc.c2.n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_val_nested_struct_access() {
        assert_eq!(
            25,
            helper_run_main_exit(
                "
val type counter {
    n: int64
}

val type counters {
    c1: counter,
    c2: counter
}

func main() ret int64 {
    let cc = alloc counters;
    cc.c1.n = 12;
    cc.c2.n = 13;
    return cc.c1.n + cc.c2.n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_hex() {
        assert_eq!(
            43794,
            helper_run_main_exit(
                "
func main() ret int32 {
    return xAb12;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_octal() {
        assert_eq!(
            28362,
            helper_run_main_exit(
                "
func main() ret int32 {
    return o67312;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_binary() {
        assert_eq!(
            153049,
            helper_run_main_exit(
                "
func main() ret int32 {
    return b100101010111011001;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_explicit_type_annotation() {
        assert_eq!(
            43794,
            helper_run_main_exit(
                "
func main() ret int32 {
    let n: int32 = xAb12 as int32;
    return n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_cast_int_types() {
        assert_eq!(
            123,
            helper_run_main_exit(
                "
func main() ret int32 {
    var a = 123 as int32;
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_cast_int_ptr_types() {
        assert_ne!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    var a = \"hello world\";
    var b = a as int64;
    var c = b as *byte;
    return b;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_sizeof_type() {
        assert_eq!(
            4,
            helper_run_main_exit(
                "
func main() ret int64 {
    return sizeof type int32;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_sizeof_var() {
        assert_eq!(
            2,
            helper_run_main_exit(
                "
func main() ret int64 {
    var b = 32 as byte;
    let n = sizeof expr b+1;
    return n+1;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_sizeof_array() {
        assert_eq!(
            16,
            helper_run_main_exit(
                "
func main() ret int64 {
    return (sizeof type [4]int32);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_sizeof_struct() {
        assert!(
            helper_run_main_exit(
                "
ref type rpair {
    x: int32,
    y: int64
}

val type vpair {
    x: int32,
    y: int64
}

func main() ret int64 {
    return (sizeof type rpair) + (sizeof type vpair);
}
"
            )
            .unwrap()
                >= 24
        );
    }

    #[test]
    fn test_sizeof_ptradd() {
        assert_eq!(
            4,
            helper_run_main_exit(
                "
func main() ret int64 {
    var ptr: *int32 = 0 as *int32;
    ptr = ptr + 1;
    return ptr as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_array_access() {
        assert_eq!(
            18,
            helper_run_main_exit(
                "
func main() ret int32 {
    var digits = [0,1,2,3,4,5,6,7,8,9];
    var i = 3;
    var num = digits[i];
    digits[i+1] = 5;
    i = i + 1;
    num = num + digits[i];
    digits[7] = 10;
    num = num + digits[7];
    return num as int32;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_array_argument() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func increase0(arr: [4]int64) ret [4]int64 {
    arr[0] = arr[0] + 1;
    return arr;
}

func increase1(arr: [4]int64) ret int64 {
    arr[1] = arr[1] + 1;
    return arr[1];
}

func main() ret int64 {
    var arr = [1,10,100,1000];
    arr = increase0(arr);
    increase1(arr);
    return arr[0] + arr[1];
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_addressof() {
        assert_ne!(
            0,
            helper_run_main_exit(
                "
func main() ret int64 {
    var num = 123;
    var addr = &num;
    return addr as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ptr_deref() {
        assert_eq!(
            65,
            helper_run_main_exit(
                "
func main() ret int64 {
    var str = \"Abc\";
    var chr = *str;
    return chr as int64;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ptr_struct_deref() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
type foo {
    x: byte
}

func main() ret byte {
    let f = alloc foo;
    f.x = 65 as byte;
    let q = deref f;
    return q.x;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_mutable_arg() {
        assert_eq!(
            13,
            helper_run_main_exit(
                "
func foo(var n: int64) ret int64 {
    n = n + 1;
    return n;
}

func main() ret int64 {
    return foo(12);
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ptridx_lvalueness() {
        assert_eq!(
            132,
            helper_run_main_exit(
                "
func foo(n: *int64) ret int64 {
    n[0] = n[0] + n[1];
    return 1;
}

func main() ret int64 {
    var a = [123,2];
    foo(&a);
    a[1] = 1;
    foo(&a);
    a[1] = 6;
    foo(&a);
    return a[0];
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_explicit_immutable_arg() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo(let n: int64) ret int64 {
    n = n + 1;
    return n;
}

func main() ret int64 {
    return foo(12);
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_type_alias() {
        assert_eq!(
            123,
            helper_run_main_exit(
                "
type main_ret = int32;

func main() ret main_ret {
    var mr: main_ret = 123 as main_ret;
    return mr;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_func_ptr_call() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
func inc(x: int64) ret int64 {
    return x + 1;
}

func double(x: int64) ret int64 {
    return x + x;
}

func main() ret int64 {
    var n = 5;
    var fp = &inc;
    n = (*fp)(n);
    fp = &double;
    n = (*fp)(n);
    return n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_func_ptr_argty() {
        assert_eq!(
            23,
            helper_run_main_exit(
                "
func inc(x: int64) ret int64 {
    return x + 1;
}

func double(x: int64) ret int64 {
    return x + x;
}

type fp = fn(int64) ret int64;

func try(n: int64, f: fp, g: fp) ret int64 {
    return (*g)((*f)(n));
}

func main() ret int64 {
    var x = 5;
    let a = try(x, &inc, &double);
    let b = try(x, &double, &inc);
    return a + b;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_while_entered() {
        assert_eq!(
            15,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 0;
    while (x>0) {
        x = x - 1;
        a = a + x;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_while_not_entered() {
        assert_eq!(
            11,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 11;
    while (x>10) {
        x = x - 1;
        a = a + x;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_while_else_not_entered() {
        assert_eq!(
            15,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 0;
    while (x>0) {
        x = x - 1;
        a = a + x;
    } else {
        a = 300;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_while_else_entered() {
        assert_eq!(
            300,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 11;
    while (x>10) {
        x = x - 1;
        a = a + x;
    } else {
        a = 300;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_return_in_while() {
        assert_eq!(
            5,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 0;
    while (x>0) {
        if (a > 3) { return a; };
        x = x - 1;
        a = a + x;
    } else {
        a = 300;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_if_return_in_while_else() {
        assert_eq!(
            300,
            helper_run_main_exit(
                "
func main() ret int64 {
    var x = 6;
    var a = 0;
    while (x>10) {
        if (a > 3) { return a; };
        x = x - 1;
        a = a + x;
    } else {
        return 300;
    };
    return a;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_refty_simple_method_call() {
        assert_eq!(
            25,
            helper_run_main_exit(
                "
ref type pair {
    x: int64,
    y: int64
}

impl pair {
    func add() ret int64 {
        return self.x + self.y;
    }
}

func main() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    return p->add();
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_valty_simple_method_call() {
        assert_eq!(
            25,
            helper_run_main_exit(
                "
val type pair {
    x: int64,
    y: int64
}

impl pair {
    func add() ret int64 {
        return self.x + self.y;
    }
}

func main() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    return p->add();
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_refty_method_call_with_args() {
        assert_eq!(
            3,
            helper_run_main_exit(
                "
ref type pair {
    x: int64,
    y: int64
}

impl pair {
    func add(n: int64, m: int64) ret pair {
        var ret = alloc pair;
        ret.x = self.x + n;
        ret.y = self.y + m;
        return ret;
    }
}

func main() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    p = p->add(5, 7);
    return p.y - p.x;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_valty_method_call_with_args() {
        assert_eq!(
            3,
            helper_run_main_exit(
                "
val type pair {
    x: int64,
    y: int64
}

impl pair {
    func add(n: int64, m: int64) ret pair {
        var ret = alloc pair;
        ret.x = self.x + n;
        ret.y = self.y + m;
        return ret;
    }
}

func main() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    p = p->add(5, 7);
    return p.y - p.x;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_argc_mismatch_err() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo() ret int64 {
    return 0;
}

func main() ret int64 {
    return foo(1,2,3);
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_argc_mismatch_ptr() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
func foo() ret int64 {
    return 0;
}

func main() ret int64 {
    let fp = &foo;
    return (*fp)(1,2,3);
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_argc_mismatch_method() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
type pair {
    x: int64,
    y: int64
}

impl pair {
    func add() ret int64 {
        return self.x + self.y;
    }
}

func main() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    return p->add(1,2,3);
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_mutable_unwritten_warning() {
        assert!(
            helper_compile_warnings(
                "
func foo() ret int64 {
    var q = 5;
    return q + 1;
}

func main() ret int64 {
    var n = 5;
    var m = foo() + n;
    return n + m;
}
"
            )
            .len()
                >= 3
        );
    }

    #[test]
    fn test_err_reserved_field_name() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
type foo {
    __field: byte
}

func main() ret int32 {
    return 0 as int32;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_alloc_stress() {
        assert_eq!(
            500,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

impl pair {
    func add(n: int64, m: int64) ret pair {
        var ret = alloc pair;
        ret.x = self.x + n;
        ret.y = self.y + m;
        return ret;
    }
}

func foo() ret int64 {
    var p = alloc pair;
    p.x = 12;
    p.y = 13;
    p = p->add(5, 7);
    return p.y - p.x;
}

func main() ret int64 {
    var i = 0;
    while (i < 500) {
        if (foo() == 3) { i = i + 1; }
        else { return i; };
    };
    return i;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_alloc_frees_in_same_func() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func foo() ret int64 {
    var p = alloc pair;
    return 0;
}

func main() ret int64 {
    foo();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_incref_leaks() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func foo() ret int64 {
    var p = incref alloc pair;
    return 0;
}

func main() ret int64 {
    foo();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_incref_decref_frees() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func foo() ret int64 {
    var p = incref alloc pair;
    decref p;
    return 0;
}

func main() ret int64 {
    foo();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_alloc_frees_after_self_call() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

impl pair {
    func foo() ret int64 {
        return 0;
    }
}

func foo() ret int64 {
    var p = alloc pair;
    return p->foo();
}

func main() ret int64 {
    foo();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_alloc_frees_after_free_call() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func bar(x: pair) ret int64 {
    return 0;
}

func foo() ret int64 {
    var p = alloc pair;
    return bar(p);
}

func main() ret int64 {
    foo();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_free_of_function_return() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func foo() ret pair {
    return alloc pair;
}

func bar() ret int64 {
    foo();
}

func main() ret int64 {
    bar();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_free_of_used_function_return() {
        assert_eq!(
            2,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func foo() ret pair {
    var p = alloc pair;
    p.x = 1;
    p.y = 2;
    return p;
}

func bar() ret int64 {
    var p = alloc pair;
    p = foo();
    return p.x + p.y;
}

func main() ret int64 {
    var n = bar();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_free_of_standalone_expr() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

func bar() ret int64 {
    alloc pair;
}

func main() ret int64 {
    bar();
    return g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_val_struct_immutable() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
val type pair {
    x: int64,
    y: int64
}

impl pair {
    func foo() ret int64 {
        self.x = self.x + 1;
        return self.y;
    }
}

func main() ret int64 {
    let p = alloc pair;
    p.x = 12;
    p->foo();
    return p.x;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_struct_mutable() {
        assert_eq!(
            13,
            helper_run_main_exit(
                "
ref type pair {
    x: int64,
    y: int64
}

impl pair {
    func foo() ret int64 {
        self.x = self.x + 1;
        return self.y;
    }
}

func main() ret int64 {
    let p = alloc pair;
    p.x = 12;
    p->foo();
    return p.x;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_alloc_frees_after_method_call() {
        assert_eq!(
            24,
            helper_run_main_exit(
                "
type pair {
    x: int64,
    y: int64
}

impl pair {
    func copy() ret pair {
        var q = alloc pair;
        q.x = self.x;
        q.y = self.y;
        return q;
    }
}

func foo() ret pair {
    var p = alloc pair;
    p.x = 22;
    return p->copy();
}

func blah() ret int64 {
    let f = foo();
    return f.x;
}

func main() ret int64 {
    return blah() + g_FreedObjects;
}        
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_getref() {
        assert!(
            helper_run_main_exit(
                "
ref type pair {
    x: int64,
    y: int64
}

func main() ret int64 {
    let p = alloc pair;
    let q = alloc pair;
    let pp = p;
    let qq = q;
    incref p;
    return getref p;
}
"
            )
            .unwrap()
                >= 2
        );
    }

    // we cannot test a failed assertion without crashing the whole thing
    #[test]
    fn test_assert_ok() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func main() ret int64 {
    assert true;
    assert 3 > 0;
    assert 12 == 12;

    return 1;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_unicode_identifiers() {
        assert_eq!(
            1,
            helper_run_main_exit(
                "
func i_use_русский日本語मानक(x: int64) ret int64 {
    let n😃 = 5;
    let ✅ = 1 + x;
    return n😃 - ✅;
}

func main() ret int64 {
    let _𔔁 = 3;
    let $𔕰 = i_use_русский日本語मानक(_𔔁);
    return $𔕰; 
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_shadow_alloca_ok() {
        assert_eq!(
            128,
            helper_run_main_exit(
                "
val type wrapper {
    x: int64
}

func main() ret int64 {
    let p = alloc wrapper;
    p.x = 123;
    let p = p.x;
    let p = p + 1;
    var p = p + 1;
    p = p + 1;
    let p = p + 2;
    return p;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_shadow_alloca_frees() {
        assert_eq!(
            129,
            helper_run_main_exit(
                "
ref type wrapper {
    x: int64
}

func foo() ret int64 {
    let p = alloc wrapper;
    p.x = 123;
    let p = p.x;
    let p = p + 1;
    var p = p + 1;
    p = p + 1;
    let p = p + 2;
    return p;
}

func main() ret int64 {
    let n = foo();
    let n = n + g_FreedObjects;
    return n;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_recursive_val_type_disallowed() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
val type foo {
    f: foo 
}

func main() ret int64 {
    let f = alloc foo;
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_indirect_recursive_val_type_allowed() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
val type foo {
    f: *foo 
}

func main() ret int64 {
    let f = alloc foo;
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_recursive_ref_type_allowed() {
        assert_eq!(
            0,
            helper_run_main_exit(
                "
ref type foo {
    f: foo 
}

func main() ret int64 {
    let f = alloc foo;
    return 0;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_free_of_nested_ref_struct() {
        assert_eq!(
            10,
            helper_run_main_exit(
                "
ref type number {
    val: int64
}

func new_number(n: int64) ret number {
    let num = alloc number;
    num.val = n;
    return num;
}

ref type pair {
    x: number,
    y: number
}

func foo() ret int64 {
    var p = alloc pair;
    p.x = new_number(3);
    p.y = new_number(4);
    return p.x.val + p.y.val;
}

func main() ret int64 {
    let n = foo();
    return n + g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_free_of_nested_mix_struct() {
        assert_eq!(
            9,
            helper_run_main_exit(
                "
ref type Rnumber {
    val: int64
}

val type Vnumber {
    val: int64
}

func new_number(n: int64) ret Rnumber {
    let num = alloc Rnumber;
    num.val = n;
    return num;
}

ref type pair {
    x: Rnumber,
    y: Vnumber
}

func foo() ret int64 {
    var p = alloc pair;
    p.x = new_number(3);
    p.y.val = 4;
    return p.x.val + p.y.val;
}

func main() ret int64 {
    let n = foo();
    return n + g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_dont_multifree_member() {
        assert_eq!(
            2,
            helper_run_main_exit(
                "
ref type object {
    a: int64,
    b: object,
    c: object
}

func foo() ret int64 {
    var o = alloc object;
    o.b = alloc object;
    o.c = o.b;
    return 0;
}

func main() ret int64 {
    return foo() + g_FreedObjects;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_no_ref_in_val_type() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
ref type foo {
    x: bool
}

val type bar {
    x: foo
}

func main() ret int64 {
    return 0;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_val_type_alloc_init() {
        assert_eq!(
            247,
            helper_run_main_exit(
                "
val type pair {
    x: int32,
    y: int64
}

func make_pair(x: int32, y: int64) ret pair {
    return alloc pair {
        x: x,
        y: y
    };
}

func main() ret int64 {
    let p = make_pair(200, 47);
    return p.x as int64 + p.y;
}"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_alloc_init() {
        assert_eq!(
            247,
            helper_run_main_exit(
                "
ref type pair {
    x: int32,
    y: int64
}

func make_pair(x: int32, y: int64) ret pair {
    return alloc pair {
        x: x,
        y: y
    };
}

func main() ret int64 {
    let p = make_pair(200, 47);
    return p.x as int64 + p.y;
}"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_init_hints() {
        assert_eq!(
            12,
            helper_run_main_exit(
                "
ref type pair {
    x: int32,
    y: int64,
    init(a: int32) {
        self.x = a;
        self.y = a as int64;
    }
}

func main() ret int64 {
    let p = alloc pair(12);
    return p.y;
}"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_init_declared_used() {
        assert_eq!(
            15,
            helper_run_main_exit(
                "
ref type ord_pair {
    max: int64,
    min: int64,
    init(x: int64, y: int64) {
        if (x > y) {
            self.max = x;
            self.min = y;
        } else {
            self.max = y;
            self.min = y;
        };
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair(12,14);
    let p2 = alloc ord_pair(15,1);
    return p1.max + p2.min;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_dealloc_declared() {
        assert_eq!(
            15,
            helper_run_main_exit(
                "
ref type ord_pair {
    max: int64,
    min: int64,
    dealloc {
        self.max = 3;
        self.min = 3;
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair{max:13,min:5};
    let p2 = alloc ord_pair{max:10,min:2};
    return p1.max + p2.min;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_dealloc_init_declared() {
        assert_eq!(
            17,
            helper_run_main_exit(
                "
ref type ord_pair {
    max: int64,
    min: int64,
    dealloc {
        self.max = 3;
        self.min = 3;
    },
    init(x: int64, y: int64) {
        if (x > y) {
            self.max = x;
            self.min = y;
        } else {
            self.max = y;
            self.min = y;
        };
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair(2,12);
    let p2 = alloc ord_pair(13,5);
    return p1.max + p2.min;
}
"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_ref_type_init_declared_not_used() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
ref type ord_pair {
    max: int64,
    min: int64,
    init(x: int64, y: int64) {
        if (x > y) {
            self.max = x;
            self.min = y;
        } else {
            self.max = y;
            self.min = y;
        };
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair;
    let p2 = alloc ord_pair;
    return p1.max + p2.min;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_ref_type_init_used_not_declared() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
ref type ord_pair {
    max: int64,
    min: int64,
}

func main() ret int64 {
    let p1 = alloc ord_pair(3);
    let p2 = alloc ord_pair(2,5);
    return p1.max + p2.min;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_val_type_init_declared() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
val type ord_pair {
    max: int64,
    min: int64,
    init(x: int64, y: int64) {
        if (x > y) {
            self.max = x;
            self.min = y;
        } else {
            self.max = y;
            self.min = y;
        };
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair;
    let p2 = alloc ord_pair(3,4);
    return p1.max + p2.min;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_val_type_dealloc_declared() {
        assert_ne!(
            0,
            helper_compile_errors(
                "
val type ord_pair {
    max: int64,
    min: int64,
    dealloc {
        let x = 1;
    }
}

func main() ret int64 {
    let p1 = alloc ord_pair;
    let p2 = alloc ord_pair(3,4);
    return p1.max + p2.min;
}
"
            )
            .len()
        );
    }

    #[test]
    fn test_global_variable() {
        assert_eq!(
            5,
            helper_run_main_exit(
                "
var counter: int64;

func increase() {
    counter = counter + 1;
}

func main() ret int64 {
    increase();
    increase();
    increase();
    increase();
    increase();

    return counter;
}
"
            )
            .unwrap()
        );
    }
}
