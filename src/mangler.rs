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

use crate::ast::{FunctionDefinition, ProperStructDecl};

pub enum SpecialMemberFunction {
    Initializer,
    BuiltinDeallocator,
}

pub fn mangle_special_method(self_decl: StructType<'_>, func: SpecialMemberFunction) -> String {
    let type_name = self_decl.get_name().unwrap().to_str().unwrap();
    format!(
        "__{}__@{}",
        type_name,
        match func {
            SpecialMemberFunction::Initializer => "init",
            SpecialMemberFunction::BuiltinDeallocator => "dealloc",
        }
    )
}

pub fn mangle_method_name(fd: &FunctionDefinition, self_decl: &ProperStructDecl) -> String {
    format!("__{}_@_{}", self_decl.name, fd.decl.name)
}
