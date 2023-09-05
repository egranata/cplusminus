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

use inkwell::values::FunctionValue;
use serde::{Deserialize, Serialize};

use crate::{
    ast::TypeDescriptor,
    builders::{scope::Scope, ty::TypeBuilder},
    iw::CompilerCore,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FunctionBomEntry {
    pub user_facing_name: String,
    pub llvm_symbol_name: String,
    pub function_type: TypeDescriptor,
}

impl FunctionBomEntry {
    pub fn new(name: &str, tb: &TypeBuilder, fv: FunctionValue<'_>) -> Self {
        let ft = tb.descriptor_for_function_type(fv.get_type()).unwrap();
        Self {
            user_facing_name: name.to_string(),
            llvm_symbol_name: fv.get_name().to_str().unwrap().to_string(),
            function_type: ft.clone(),
        }
    }

    pub fn import<'a>(
        &self,
        iw: &CompilerCore<'a>,
        scope: &Scope<'a>,
    ) -> Option<FunctionValue<'a>> {
        use inkwell::module::Linkage::External;

        let tb = TypeBuilder::new(iw.clone());
        if let Some(fn_type) = tb.function_type_for_descriptor(scope, &self.function_type) {
            let fv = iw
                .module
                .add_function(&self.llvm_symbol_name, fn_type, Some(External));
            if scope.insert_function(&self.user_facing_name, fv, true) {
                return Some(fv);
            }
        }

        None
    }
}
