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

use inkwell::values::GlobalValue;
use serde::{Deserialize, Serialize};

use crate::{
    ast::{TokenSpan, TypeDescriptor},
    builders::{
        scope::{Scope, VarInfo},
        ty::TypeBuilder,
    },
    iw::CompilerCore,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VariableBomEntry {
    pub user_facing_name: String,
    pub underlying_type: TypeDescriptor,
}

impl VariableBomEntry {
    pub fn new(name: &str, udt: &TypeDescriptor) -> Self {
        Self {
            user_facing_name: name.to_string(),
            underlying_type: udt.clone(),
        }
    }

    pub fn import<'a>(&self, iw: &CompilerCore<'a>, scope: &Scope<'a>) -> Option<GlobalValue<'a>> {
        let tb = TypeBuilder::new(iw.clone());
        let var_type = tb
            .llvm_type_by_descriptor(scope, &self.underlying_type)
            .unwrap();
        let gv = CompilerCore::make_global(
            &iw.module,
            &self.user_facing_name,
            var_type,
            None,
            inkwell::module::Linkage::AvailableExternally,
            false,
        );

        let vi = VarInfo::new(
            TokenSpan::origin(),
            self.user_facing_name.clone(),
            gv.as_pointer_value(),
            false,
            true,
            false,
        );
        scope.insert_variable(&self.user_facing_name, vi, true);
        Some(gv)
    }
}
