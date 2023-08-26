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
    context::Context,
    types::{BasicMetadataTypeEnum, BasicTypeEnum, StructType},
    values::{BasicValue, GlobalValue},
};

use crate::{
    builders::{refcount::find_sys_dealloc_for_type, ty::TypeBuilder},
    iw::CompilerCore,
    mangler::mangle_metadata_symbol,
};

fn build_metadata_type(c: &Context) -> StructType<'_> {
    let __metadata_t = c.opaque_struct_type("__metadata_t");
    let metadata_ptr = __metadata_t.ptr_type(Default::default());
    let void = c.void_type();
    let byte = c.i8_type();
    let i64 = c.i64_type();
    let string = byte.ptr_type(Default::default());
    let dealloc_f_ty = void
        .fn_type(&[BasicMetadataTypeEnum::PointerType(metadata_ptr)], false)
        .ptr_type(Default::default());
    let fields = [
        BasicTypeEnum::PointerType(string),       // type name
        BasicTypeEnum::PointerType(dealloc_f_ty), // sys dealloc calls usr dealloc anyway
        BasicTypeEnum::IntType(i64),              // size of type
    ];
    __metadata_t.set_body(&fields, false);
    __metadata_t
}

#[derive(Clone)]
pub struct Metadata<'a> {
    pub metadata_type: StructType<'a>,
}

impl<'a> Metadata<'a> {
    pub fn build(c: &'a Context) -> Metadata<'a> {
        Metadata {
            metadata_type: build_metadata_type(c),
        }
    }

    pub fn import_metadata_for_type(
        &self,
        iw: &CompilerCore<'a>,
        ty: StructType<'a>,
    ) -> GlobalValue<'a> {
        let symbol_name = mangle_metadata_symbol(ty);
        let meta = iw.module.add_global(self.metadata_type, None, &symbol_name);
        meta.set_linkage(inkwell::module::Linkage::AvailableExternally);
        meta
    }

    pub fn build_metadata_for_type<'x>(
        &self,
        iw: &CompilerCore<'a>,
        tb: &TypeBuilder<'x>,
        ty: StructType<'a>,
    ) -> Option<GlobalValue<'a>> {
        if let Some(sd) = tb.structure_by_llvm_type(ty) {
            let sys_dealloc = find_sys_dealloc_for_type(iw, ty)
                .as_global_value()
                .as_pointer_value();
            let sys_dealloc = sys_dealloc.as_basic_value_enum();
            let sizeof = ty.size_of().unwrap().as_basic_value_enum();

            let builder = iw.context.create_builder();
            let void_f = iw.builtins.void.fn_type(&[], false);
            let dummy_f = iw.module.add_function(
                "__build_metadata_for_type__dummy",
                void_f,
                Some(inkwell::module::Linkage::Internal),
            );
            let dummy_bb = iw.context.append_basic_block(dummy_f, "entry");
            builder.position_at_end(dummy_bb);
            builder.build_return(None);

            let name = &sd.name;
            let name = builder.build_global_string_ptr(name, "");
            name.set_unnamed_addr(false);
            name.set_unnamed_address(inkwell::values::UnnamedAddress::None);
            let name = name.as_pointer_value().as_basic_value_enum();
            let value = self
                .metadata_type
                .const_named_struct(&[name, sys_dealloc, sizeof]);
            let symbol_name = mangle_metadata_symbol(ty);
            let meta = iw.module.add_global(self.metadata_type, None, &symbol_name);
            meta.set_initializer(&value);
            meta.set_constant(true);
            meta.set_linkage(inkwell::module::Linkage::External);

            Some(meta)
        } else {
            None
        }
    }

    pub fn find_metadata_for_type(
        &self,
        iw: &CompilerCore<'a>,
        ty: StructType<'a>,
    ) -> Option<GlobalValue<'a>> {
        let name = mangle_metadata_symbol(ty);
        iw.module.get_global(&name)
    }
}
