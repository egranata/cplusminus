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
    ast::{FunctionDecl, FunctionDefinition, TypeDescriptor},
    builders::ty::TypeBuilder,
};

pub enum SpecialMemberFunction {
    Initializer,
    UserDeallocator,
    BuiltinDeallocator,
}

const CPM_MANGLE_PREFIX: &str = "__X";

const CPM_SPECIAL_METHOD_PREFIX: char = 'S';
const CPM_REGULAR_METHOD_PREFIX: char = 'D';
const CPM_FREE_FUNCTION_PREFIX: char = 'F';
const CPM_TYPE_METADATA_PREFIX: char = 'M';

fn do_mangle(item_prefix: char, items: &[&str]) -> String {
    let items: Vec<String> = items
        .iter()
        .map(|item| format!("{}{}", item.len(), item))
        .collect();

    format!("{}{}{}", CPM_MANGLE_PREFIX, item_prefix, items.join(""))
}

pub fn mangle_type_descriptor(td: &TypeDescriptor) -> String {
    match td {
        TypeDescriptor::Name(name) => {
            format!("N{}{}", name.len(), name)
        }
        TypeDescriptor::Pointer(pointee) => {
            format!("P{}", mangle_type_descriptor(pointee.as_ref()))
        }
        TypeDescriptor::Array(item, len) => {
            format!("R{}{}", len, mangle_type_descriptor(item))
        }
        TypeDescriptor::Function(fd) => {
            let ret = if let Some(ret_type) = fd.ret.as_ref() {
                mangle_type_descriptor(ret_type)
            } else {
                String::from("V")
            };
            let len = fd.args.len();
            let args: Vec<_> = fd.args.iter().map(mangle_type_descriptor).collect();
            let args = args.join("");
            format!("F{}{}{}", ret, len, args)
        }
        TypeDescriptor::Tuple(td) => {
            let len = td.len();
            let items: Vec<_> = td.iter().map(mangle_type_descriptor).collect();
            let items = items.join("");
            format!("T{}{}", len, items)
        }
    }
}

pub fn mangle_special_method(
    self_decl: StructType<'_>,
    func: SpecialMemberFunction,
    imp: Option<TypeDescriptor>,
) -> String {
    assert!(!TypeBuilder::is_tuple_type(self_decl));

    let type_name = self_decl.get_name().unwrap().to_str().unwrap();
    let func_name = match func {
        SpecialMemberFunction::Initializer => {
            assert!(imp.is_some());
            format!("init{}", mangle_type_descriptor(&imp.unwrap()))
        }
        SpecialMemberFunction::UserDeallocator => {
            assert!(imp.is_none());
            String::from("drop")
        }
        SpecialMemberFunction::BuiltinDeallocator => {
            assert!(imp.is_none());
            String::from("dealloc")
        }
    };

    do_mangle(CPM_SPECIAL_METHOD_PREFIX, &[type_name, &func_name])
}

pub fn mangle_method_name(fd: &FunctionDefinition, self_name: &str) -> String {
    let mangled_type = mangle_type_descriptor(&fd.decl.ty);
    do_mangle(
        CPM_REGULAR_METHOD_PREFIX,
        &[self_name, &fd.decl.name, &mangled_type],
    )
}

pub fn mangle_function_name(fd: &FunctionDecl) -> String {
    if fd.name.starts_with(CPM_MANGLE_PREFIX) {
        fd.name.to_string()
    } else {
        do_mangle(CPM_FREE_FUNCTION_PREFIX, &[&fd.name])
    }
}

pub fn mangle_metadata_symbol(ty: StructType<'_>) -> String {
    let type_name = ty.get_name().unwrap().to_str().unwrap();

    do_mangle(CPM_TYPE_METADATA_PREFIX, &[type_name])
}
