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

use inkwell::values::PointerValue;

use crate::{ast::Location, codegen::MutableOf};

#[derive(Clone)]
pub struct VarInfo<'a> {
    pub loc: Location,
    pub name: String,
    pub alloca: PointerValue<'a>,
    pub rw: bool,
    pub written: Rc<RefCell<bool>>,
}

impl<'a> VarInfo<'a> {
    pub fn new(loc: Location, name: String, alloca: PointerValue<'a>, rw: bool) -> Self {
        Self {
            loc,
            name,
            alloca,
            rw,
            written: Rc::new(RefCell::new(false)),
        }
    }
}

#[derive(Clone)]
pub struct HierarchicalStorage<T: Clone> {
    parent: Option<Rc<HierarchicalStorage<T>>>,
    pub storage: MutableOf<HashMap<String, T>>,
}

impl<T: Clone> HierarchicalStorage<T> {
    pub fn root() -> Rc<Self> {
        Rc::new(Self {
            parent: None,
            storage: Default::default(),
        })
    }

    pub fn child(parent: &Rc<HierarchicalStorage<T>>) -> Rc<Self> {
        Rc::new(Self {
            parent: Some(parent.clone()),
            storage: Default::default(),
        })
    }

    pub fn keys(&self) -> Vec<String> {
        let borrow = self.storage.borrow();
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
        let borrow = self.storage.borrow();
        borrow.values().for_each(f);
    }

    pub fn find(&self, name: &str, recurse: bool) -> Option<T> {
        if let Some(pv) = self.storage.borrow().get(name) {
            Some(pv.clone())
        } else if recurse && self.parent.is_some() {
            self.parent.as_ref().unwrap().find(name, true)
        } else {
            None
        }
    }

    pub fn insert(&self, name: &str, val: T, overwrite: bool) -> bool {
        if !overwrite && self.storage.borrow().get(name).is_some() {
            false
        } else {
            self.storage.borrow_mut().insert(name.to_string(), val);
            true
        }
    }
}

#[derive(Clone)]
pub struct ScopeObject<'a> {
    pub variables: Rc<HierarchicalStorage<VarInfo<'a>>>,
}

impl<'a> ScopeObject<'a> {
    pub fn root() -> Rc<Self> {
        Rc::new(Self {
            variables: HierarchicalStorage::root(),
        })
    }

    pub fn child(parent: &Rc<ScopeObject<'a>>) -> Rc<Self> {
        Rc::new(Self {
            variables: HierarchicalStorage::child(&parent.variables),
        })
    }

    pub fn find_variable(&self, name: &str, recurse: bool) -> Option<VarInfo<'a>> {
        self.variables.find(name, recurse)
    }

    pub fn insert_variable(&self, name: &str, val: VarInfo<'a>, overwrite: bool) -> bool {
        self.variables.insert(name, val, overwrite)
    }
}

pub type Scope<'a> = Rc<ScopeObject<'a>>;
