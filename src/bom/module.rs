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
    fs::{self, File},
    path::Path,
};

use serde::{Deserialize, Serialize};

use super::{
    alias::AliasBomEntry, function::FunctionBomEntry, strct::StructBomEntry,
    variable::VariableBomEntry,
};

const BILL_OF_MATERIALS_VERSION: i32 = 1;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BillOfMaterials {
    pub version: i32,
    pub functions: Vec<FunctionBomEntry>,
    pub aliases: Vec<AliasBomEntry>,
    pub variables: Vec<VariableBomEntry>,
    pub structs: Vec<StructBomEntry>,
}

impl Default for BillOfMaterials {
    fn default() -> Self {
        Self {
            version: BILL_OF_MATERIALS_VERSION,
            functions: Default::default(),
            aliases: Default::default(),
            variables: Default::default(),
            structs: Default::default(),
        }
    }
}

impl BillOfMaterials {
    pub fn write(&self, out: &Path) -> bool {
        use serde_json::to_string_pretty;
        use std::io::Write;

        if let Ok(text) = to_string_pretty(self) {
            if let Ok(mut dest) = File::create(out) {
                return write!(dest, "{text}").is_ok();
            }
        }

        false
    }

    pub fn load(inp: &Path) -> Option<Self> {
        use serde_json::from_str;

        if let Ok(text) = fs::read_to_string(inp) {
            if let Ok(this) = from_str::<Self>(&text) {
                return if this.version != BILL_OF_MATERIALS_VERSION {
                    None
                } else {
                    Some(this)
                };
            }
        }

        None
    }
}
