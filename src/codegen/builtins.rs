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

use std::collections::HashMap;

use inkwell::{
    context::Context,
    types::{BasicTypeEnum, FloatType, IntType, VoidType},
    values::{FloatValue, IntValue},
};

#[derive(Clone, Copy)]
pub struct BuiltinTypes<'a> {
    pub bool: IntType<'a>,
    pub byte: IntType<'a>,
    pub int32: IntType<'a>,
    pub int64: IntType<'a>,
    pub float32: FloatType<'a>,
    pub float64: FloatType<'a>,
    pub void: VoidType<'a>,
    pub default_int_type: IntType<'a>,
    pub default_float_type: FloatType<'a>,
}

impl<'a> BuiltinTypes<'a> {
    pub fn new(c: &'a Context) -> Self {
        Self {
            bool: c.bool_type(),
            byte: c.i8_type(),
            int32: c.i32_type(),
            int64: c.i64_type(),
            float32: c.f32_type(),
            float64: c.f64_type(),
            void: c.void_type(),
            default_int_type: c.i64_type(),
            default_float_type: c.f64_type(),
        }
    }

    pub fn zero(&self, i: IntType<'a>) -> IntValue<'a> {
        i.const_zero()
    }

    pub fn one(&self, i: IntType<'a>) -> IntValue<'a> {
        self.n(1, i)
    }

    pub fn n(&self, val: u64, i: IntType<'a>) -> IntValue<'a> {
        i.const_int(val, false)
    }

    pub fn flt_zero(&self, i: FloatType<'a>) -> FloatValue<'a> {
        i.const_zero()
    }

    pub fn flt_one(&self, i: FloatType<'a>) -> FloatValue<'a> {
        self.flt_n(1.0, i)
    }

    pub fn flt_n(&self, val: f64, i: FloatType<'a>) -> FloatValue<'a> {
        i.const_float(val)
    }

    pub fn get(&self, name: &str) -> Option<BasicTypeEnum<'a>> {
        self.builtin_types_map().get(name).copied()
    }

    pub fn builtin_types_map(&self) -> HashMap<String, BasicTypeEnum<'a>> {
        let ret = HashMap::from([
            (String::from("bool"), BasicTypeEnum::IntType(self.bool)),
            (String::from("byte"), BasicTypeEnum::IntType(self.byte)),
            (String::from("int32"), BasicTypeEnum::IntType(self.int32)),
            (String::from("int64"), BasicTypeEnum::IntType(self.int64)),
            (
                String::from("float32"),
                BasicTypeEnum::FloatType(self.float32),
            ),
            (
                String::from("float64"),
                BasicTypeEnum::FloatType(self.float64),
            ),
        ]);

        ret
    }
}
