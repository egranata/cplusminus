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
    execution_engine::{JitFunction, UnsafeFunctionPointer},
    OptimizationLevel,
};

use crate::iw::CompilerCore;

pub fn get_runnable_function<'a, T: UnsafeFunctionPointer>(
    iw: &CompilerCore<'a>,
    name: &str,
    optimize: bool,
) -> Option<JitFunction<'a, T>> {
    let ol = if optimize {
        OptimizationLevel::Aggressive
    } else {
        OptimizationLevel::None
    };
    let ee = iw
        .module
        .create_jit_execution_engine(ol)
        .expect("llvm error");
    unsafe { ee.get_function(name).map_or_else(|_| None, Some) }
}
