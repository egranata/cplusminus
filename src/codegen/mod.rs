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
    cell::{OnceCell, RefCell},
    rc::Rc,
};

pub mod assertion;
pub mod builtins;
pub mod callable;
pub mod metadata;
pub mod structure;

pub type MutableOf<T> = Rc<RefCell<T>>;
pub type OnceOf<T> = Rc<OnceCell<T>>;
