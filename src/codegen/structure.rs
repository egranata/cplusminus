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

use std::{cell::OnceCell, fmt::Display, iter::zip, rc::Rc};

use inkwell::{
    types::{BasicTypeEnum, StructType},
    values::FunctionValue,
};

use crate::ast::{FieldDecl, ImplDecl, MethodDecl, ProperStructDecl};

use super::MutableOf;

#[derive(Clone, Debug)]
pub struct Field<'a> {
    pub decl: FieldDecl,
    pub ty: BasicTypeEnum<'a>,
}

#[derive(Clone, Debug)]
pub struct Method<'a> {
    pub decl: MethodDecl,
    pub func: FunctionValue<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryStrategy {
    ByValue,
    ByReference,
}

impl Display for MemoryStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            if self == &MemoryStrategy::ByValue {
                "val"
            } else {
                "ref"
            }
        )
    }
}

#[derive(Clone, Debug)]
pub struct Structure<'a> {
    pub decl: ProperStructDecl,
    pub str_ty: StructType<'a>,
    pub var_ty: BasicTypeEnum<'a>,
    pub ms: MemoryStrategy,
    pub implementations: MutableOf<Vec<ImplDecl>>,
    pub fields: MutableOf<Vec<Field<'a>>>,
    pub methods: MutableOf<Vec<Method<'a>>>,
    pub init: Rc<OnceCell<FunctionValue<'a>>>,
    pub dealloc: Rc<OnceCell<FunctionValue<'a>>>,
}

impl<'a> Structure<'a> {
    pub fn field_idx_by_name(&self, name: &str) -> Option<usize> {
        let fields: &Vec<Field<'a>> = &self.fields.borrow();
        let iter = zip(fields.iter(), 0..fields.len());
        for (fd, idx) in iter {
            if fd.decl.name == name {
                return Some(idx);
            };
        }

        None
    }

    pub fn field_type_by_name(&self, name: &str) -> Option<BasicTypeEnum<'a>> {
        let fields: &Vec<Field<'a>> = &self.fields.borrow();
        for fd in fields.iter() {
            if fd.decl.name == name {
                return Some(fd.ty);
            };
        }

        None
    }

    pub fn method_by_name(&self, name: &str) -> Option<Method<'a>> {
        for method in self.methods.borrow().iter() {
            if method.decl.imp.decl.name == name {
                return Some(method.clone());
            }
        }
        None
    }
}
