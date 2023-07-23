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

use inkwell::types::StructType;
use serde::{Deserialize, Serialize};

use crate::{
    ast::TypeDescriptor,
    builders::{scope::Scope, ty::TypeBuilder},
    codegen::structure::{MemoryStrategy, Method, Structure},
    iw::CompilerCore,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldBomEntry {
    pub name: String,
    pub underlying_type: TypeDescriptor,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MethodBomEntry {
    pub user_facing_name: String,
    pub underlying_func_llvm_name: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StructBomEntry {
    pub name: String,
    pub ms: MemoryStrategy,
    pub fields: Vec<FieldBomEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImplBomEntry {
    pub struct_name: String,
    pub methods: Vec<MethodBomEntry>,
}

impl StructBomEntry {
    pub fn new(udt: &Structure<'_>) -> Self {
        let fields: Vec<FieldBomEntry> = udt
            .fields
            .borrow()
            .iter()
            .map(|field| FieldBomEntry {
                name: field.name.clone(),
                underlying_type: TypeBuilder::descriptor_by_llvm_type(field.ty).unwrap(),
            })
            .collect();
        Self {
            name: udt.name.clone(),
            ms: udt.ms,
            fields,
        }
    }

    pub fn import<'a>(&self, iw: &CompilerCore<'a>, scope: &Scope<'a>) -> Option<StructType<'a>> {
        let tb = TypeBuilder::new(iw.clone());
        tb.build_structure_from_bom(scope, self)
    }
}

impl ImplBomEntry {
    pub fn new(sd: &Structure<'_>) -> Self {
        Self {
            struct_name: sd.name.clone(),
            methods: vec![],
        }
    }

    pub fn add_method(&mut self, method: &Method) -> &mut Self {
        self.methods.push(MethodBomEntry {
            user_facing_name: method.name.clone(),
            underlying_func_llvm_name: method.func.get_name().to_str().unwrap().to_owned(),
        });
        self
    }

    pub fn import<'a>(&self, iw: &CompilerCore<'a>, sd: &Structure<'a>) -> Option<StructType<'a>> {
        for method in &self.methods {
            // ok to look for a function directly in the LLVM module since we're
            // not doing scoping, but just trying to detect the symbol itself
            if let Some(func) = iw.module.get_function(&method.underlying_func_llvm_name) {
                sd.methods.borrow_mut().push(Method {
                    name: method.user_facing_name.clone(),
                    func,
                });
            } else {
                return None;
            }
        }

        Some(sd.str_ty)
    }
}
