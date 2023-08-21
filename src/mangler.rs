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

use crate::{
    ast::{FunctionDecl, FunctionDefinition},
    builders::ty::TypeBuilder,
};

pub enum SpecialMemberFunction {
    Initializer,
    UserDeallocator,
    BuiltinDeallocator,
}

const CPM_MANGLE_PREFIX: &str = "__X";

pub fn mangle_special_method(self_decl: StructType<'_>, func: SpecialMemberFunction) -> String {
    assert!(!TypeBuilder::is_tuple_type(self_decl));

    let type_name = self_decl.get_name().unwrap().to_str().unwrap();
    let func_name = match func {
        SpecialMemberFunction::Initializer => "init",
        SpecialMemberFunction::UserDeallocator => "drop",
        SpecialMemberFunction::BuiltinDeallocator => "dealloc",
    };
    format!(
        "{}S__{}{}_{}{}",
        CPM_MANGLE_PREFIX,
        type_name.len(),
        type_name,
        func_name.len(),
        func_name
    )
}

pub fn mangle_method_name(fd: &FunctionDefinition, self_name: &str) -> String {
    format!(
        "{}F__{}{}__{}{}",
        CPM_MANGLE_PREFIX,
        self_name.len(),
        self_name,
        fd.decl.name.len(),
        fd.decl.name
    )
}

pub fn mangle_function_name(fd: &FunctionDecl) -> String {
    if fd.name.starts_with(CPM_MANGLE_PREFIX) {
        fd.name.to_string()
    } else {
        format!("{}_{}{}", CPM_MANGLE_PREFIX, fd.name.len(), fd.name)
    }
}

pub fn mangle_metadata_symbol(ty: StructType<'_>) -> String {
    let type_name = ty.get_name().unwrap().to_str().unwrap();

    format!("{}M__{}{}", CPM_MANGLE_PREFIX, type_name.len(), type_name,)
}
