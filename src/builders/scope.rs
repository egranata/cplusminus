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

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use inkwell::{
    types::BasicTypeEnum,
    values::{FunctionValue, PointerValue},
};

use crate::{ast::TokenSpan, codegen::MutableOf};

#[derive(Clone)]
pub struct VarInfo<'a> {
    pub loc: TokenSpan,
    pub name: String,
    pub alloca: PointerValue<'a>,
    pub rw: bool,
    pub is_arg: bool,
    pub referenced: Rc<RefCell<bool>>,
    pub written: Rc<RefCell<bool>>,
    pub is_implicit: bool,
}

impl<'a> VarInfo<'a> {
    pub fn new(
        loc: TokenSpan,
        name: String,
        alloca: PointerValue<'a>,
        is_arg: bool,
        rw: bool,
        implicit: bool,
    ) -> Self {
        Self {
            loc,
            name,
            alloca,
            rw,
            is_arg,
            referenced: Rc::new(RefCell::new(false)),
            written: Rc::new(RefCell::new(false)),
            is_implicit: implicit,
        }
    }
}

impl<'a> VarInfo<'a> {
    pub fn is_unreferenced(&self, ignore_underscore: bool, ignore_arg: bool) -> bool {
        let referenced = *self.referenced.borrow();
        if self.is_implicit {
            false
        } else {
            !(referenced
                || (self.is_arg && ignore_arg)
                || (ignore_underscore && self.name.starts_with('_')))
        }
    }

    pub fn is_unwritten(&self) -> bool {
        let written = *self.written.borrow();
        if self.is_implicit || written {
            false
        } else {
            self.rw
        }
    }
}

#[derive(Clone)]
pub enum HierarchicalStorage<T: Clone> {
    Root(MutableOf<HashMap<String, T>>),
    Child(Rc<HierarchicalStorage<T>>, MutableOf<HashMap<String, T>>),
}

impl<T: Clone> HierarchicalStorage<T> {
    pub fn root() -> Rc<Self> {
        Rc::new(Self::Root(Default::default()))
    }

    pub fn child(parent: &Rc<HierarchicalStorage<T>>) -> Rc<Self> {
        Rc::new(Self::Child(parent.clone(), Default::default()))
    }

    fn storage(&self) -> &MutableOf<HashMap<String, T>> {
        match self {
            HierarchicalStorage::Root(storage) => storage,
            HierarchicalStorage::Child(_, storage) => storage,
        }
    }

    pub fn keys(&self) -> Vec<String> {
        let borrow = self.storage().borrow();
        let borrow_keys: Vec<&String> = borrow.keys().collect();
        let mut new_keys: Vec<String> = vec![];
        borrow_keys
            .iter()
            .for_each(|k| new_keys.push(k.to_string()));
        new_keys
    }

    pub fn values<F>(&self, f: F)
    where
        F: FnMut(&T),
    {
        let borrow = self.storage().borrow();
        borrow.values().for_each(f);
    }

    pub fn find(&self, name: &str, recurse: bool) -> Option<T> {
        match self {
            HierarchicalStorage::Root(storage) => storage.borrow().get(name).cloned(),
            HierarchicalStorage::Child(parent, storage) => {
                return if let Some(pv) = storage.borrow().get(name) {
                    Some(pv.clone())
                } else if recurse {
                    parent.find(name, recurse)
                } else {
                    None
                }
            }
        }
    }

    pub fn insert(&self, name: &str, val: T, overwrite: bool) -> bool {
        if !overwrite && self.find(name, false).is_some() {
            false
        } else {
            self.storage().borrow_mut().insert(name.to_string(), val);
            true
        }
    }
}

#[derive(Clone)]
pub struct ScopeObject<'a> {
    pub variables: Rc<HierarchicalStorage<VarInfo<'a>>>,
    pub aliases: Rc<HierarchicalStorage<BasicTypeEnum<'a>>>,
    pub functions: Rc<HierarchicalStorage<FunctionValue<'a>>>,
}

impl<'a> ScopeObject<'a> {
    pub fn root() -> Rc<Self> {
        Rc::new(Self {
            variables: HierarchicalStorage::root(),
            aliases: HierarchicalStorage::root(),
            functions: HierarchicalStorage::root(),
        })
    }

    pub fn child(parent: &Rc<ScopeObject<'a>>) -> Rc<Self> {
        Rc::new(Self {
            variables: HierarchicalStorage::child(&parent.variables),
            aliases: HierarchicalStorage::child(&parent.aliases),
            functions: HierarchicalStorage::child(&parent.functions),
        })
    }

    pub fn find_variable(&self, name: &str, recurse: bool) -> Option<VarInfo<'a>> {
        self.variables.find(name, recurse)
    }

    pub fn insert_variable(&self, name: &str, val: VarInfo<'a>, overwrite: bool) -> bool {
        self.variables.insert(name, val, overwrite)
    }

    pub fn find_alias(&self, name: &str, recurse: bool) -> Option<BasicTypeEnum<'a>> {
        self.aliases.find(name, recurse)
    }

    pub fn insert_alias(&self, name: &str, val: BasicTypeEnum<'a>, overwrite: bool) -> bool {
        self.aliases.insert(name, val, overwrite)
    }

    pub fn find_function(&self, name: &str, recurse: bool) -> Option<FunctionValue<'a>> {
        self.functions.find(name, recurse)
    }

    pub fn insert_function(&self, name: &str, val: FunctionValue<'a>, overwrite: bool) -> bool {
        self.functions.insert(name, val, overwrite)
    }
}

impl<'a> ScopeObject<'a> {
    pub fn emit_warnings_for_locals(
        &self,
        diagnostics: &mut crate::driver::diags::Diagnostics,
        ignore_underscore: bool,
        ignore_arg: bool,
    ) {
        self.variables.values(|vi| {
            // ignore args, they will be done at the function level
            if vi.is_unreferenced(ignore_underscore, ignore_arg) {
                diagnostics.warning(crate::err::CompilerWarning::new(
                    vi.loc,
                    crate::err::Warning::LocalValueNeverAccessed(vi.name.clone()),
                ));
            } else if vi.is_unwritten() {
                diagnostics.warning(crate::err::CompilerWarning::new(
                    vi.loc,
                    crate::err::Warning::MutableValueNeverWrittenTo(vi.name.clone()),
                ));
            }
        });
    }
}

pub type Scope<'a> = Rc<ScopeObject<'a>>;
