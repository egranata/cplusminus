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

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    values::{BasicValueEnum, FunctionValue},
};

use crate::{ast::TokenSpan, builders::ty::TypeBuilder, iw::CompilerCore};

#[derive(Clone)]
pub struct Assertion<'a> {
    pub assert_f: FunctionValue<'a>,
}

fn build_assert_func<'a>(c: &'a Context, m: &Module<'a>) -> FunctionValue<'a> {
    let byte = c.i8_type();
    let string = byte.ptr_type(Default::default());
    let i32 = c.i32_type();
    let void = c.void_type();

    let fn_type = void.fn_type(&[i32.into(), string.into(), i32.into()], false);
    let fn_value = m.add_function(
        "__assert_f",
        fn_type,
        Some(inkwell::module::Linkage::AvailableExternally),
    );

    fn_value
}

impl<'a> Assertion<'a> {
    pub fn build(c: &'a Context, m: &Module<'a>) -> Assertion<'a> {
        Assertion {
            assert_f: build_assert_func(c, m),
        }
    }

    pub fn build_assertion(
        &self,
        iw: &CompilerCore<'a>,
        builder: &Builder<'a>,
        at: TokenSpan,
        val: BasicValueEnum<'a>,
    ) {
        assert!(TypeBuilder::is_boolean_basic(val.get_type()));
        let val = builder.build_int_cast(val.into_int_value(), iw.builtins.int32, "");
        let file = iw.source.path_to_string();
        let file = builder.build_global_string_ptr(&file, "");
        let line = iw.source.index_to_location(at.start).line;
        let line = iw.builtins.int32.const_int(line.try_into().unwrap(), false);

        builder.build_call(
            self.assert_f,
            &[val.into(), file.as_pointer_value().into(), line.into()],
            "",
        );
    }
}
