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

use inkwell::types::BasicTypeEnum;
use serde::{Deserialize, Serialize};

use crate::{
    ast::TypeDescriptor,
    builders::{scope::Scope, ty::TypeBuilder},
    iw::CompilerCore,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AliasBomEntry {
    pub user_facing_name: String,
    pub underlying_type: TypeDescriptor,
}

impl AliasBomEntry {
    pub fn new(name: &str, udt: &TypeDescriptor) -> Self {
        Self {
            user_facing_name: name.to_string(),
            underlying_type: udt.clone(),
        }
    }

    pub fn import<'a>(
        &self,
        iw: &CompilerCore<'a>,
        scope: &Scope<'a>,
    ) -> Option<BasicTypeEnum<'a>> {
        let tb = TypeBuilder::new(iw.clone());
        tb.alias(scope, &self.user_facing_name, &self.underlying_type)
    }
}
