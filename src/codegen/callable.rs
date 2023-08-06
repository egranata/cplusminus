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
    types::FunctionType,
    values::{BasicMetadataValueEnum, FunctionValue, PointerValue},
};

#[derive(Clone, Debug)]
pub enum Callable<'a> {
    Fn(FunctionValue<'a>),
    Ptr(PointerValue<'a>, FunctionType<'a>),
}

impl<'a> Callable<'a> {
    pub fn from_function(f: FunctionValue<'a>) -> Self {
        Self::Fn(f)
    }

    pub fn from_pointer(p: PointerValue<'a>) -> Option<Self> {
        let pt = p.get_type().get_element_type();
        if pt.is_function_type() {
            Some(Self::Ptr(p, pt.into_function_type()))
        } else {
            None
        }
    }

    pub fn callee(&self) -> inkwell::values::CallableValue<'a> {
        use inkwell::values::CallableValue as CV;

        match self {
            Callable::Fn(f) => CV::from(*f),
            Callable::Ptr(p, _) => CV::try_from(*p).unwrap(),
        }
    }

    pub fn is_vararg(&self) -> bool {
        match self {
            Callable::Fn(f) => f.get_type().is_var_arg(),
            Callable::Ptr(_, ft) => ft.is_var_arg(),
        }
    }

    pub fn argc(&self) -> usize {
        match self {
            Callable::Fn(f) => f.count_params() as usize,
            Callable::Ptr(_, ft) => ft.count_param_types() as usize,
        }
    }

    pub fn fn_type(&self) -> FunctionType<'a> {
        match self {
            Callable::Fn(f) => f.get_type(),
            Callable::Ptr(_, ft) => *ft,
        }
    }

    pub fn typecheck_call(&self, args: &[BasicMetadataValueEnum]) -> bool {
        self.is_vararg() || args.len() == self.argc()
    }
}
