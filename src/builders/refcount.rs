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
    module::{Linkage, Module},
    types::{BasicMetadataTypeEnum, BasicTypeEnum, StructType},
    values::{
        AnyValue, BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntValue, PointerValue,
    },
};

use crate::{
    codegen::structure::{MemoryStrategy, Structure},
    iw::CompilerCore,
    mangler::mangle_special_method,
};

use super::ty::TypeBuilder;

// The fundamental principle of this model is that there are two types of references: owned and borrowed
// Owned: whoever is currently touching this reference needs to either hold on to it or free it;
// Borrowed: at least one other party is holding on to this reference for now;
// "for now" is generally understood to be within the context of a single function
// The main operations are inc/dec; inc adds 1 to the reference count, dec subtracts 1 unless
// the count is already 0, then it just frees the object with no further ado
// A borrowed reference can be owned by means of storing it in a variable
// An owned reference can become borrowed by setting it to a temporary object and demanding it be dec on function exit
// alloc returns a reference at 0, and functions return their values at 0
// the expression alloc foo is equivalent to
// var tmp = alloc foo; tmp (at 0) on_exit { dec(tmp) }
// the statement alloc foo is equivalent to
// var tmp = alloc foo; tmp (at 0) on_exit { dec(tmp) }
// var tmp1 = tmp; tmp (at 1) on exit { dec(tmp1) }
// var p = blah implies inc of blah
// q = blah implies dec of q's old value and inc of blah
// return blah implies inc of blah
// This model is inspired rather liberally by both Python and C++ reference counting models

fn build_refcount_type(c: &Context) -> StructType<'_> {
    let __refcount_t = c.opaque_struct_type("__refcount_t");
    let refcount_ptr = __refcount_t.ptr_type(Default::default());
    let void = c.void_type();
    let dealloc_f_ty = void
        .fn_type(&[BasicMetadataTypeEnum::PointerType(refcount_ptr)], false)
        .ptr_type(Default::default());
    let i64 = c.i64_type();
    let i64_ptr = i64.ptr_type(Default::default());
    let fields = [
        BasicTypeEnum::IntType(i64),
        BasicTypeEnum::PointerType(dealloc_f_ty),
        BasicTypeEnum::PointerType(dealloc_f_ty),
        BasicTypeEnum::PointerType(i64_ptr),
    ];
    __refcount_t.set_body(&fields, false);
    __refcount_t
}

fn build_allocref_prototype<'a>(m: &Module<'a>, c: &'a Context) -> FunctionValue<'a> {
    let int64 = c.i64_type();
    let refcount_t = int64.ptr_type(Default::default());
    let arg_ty = BasicMetadataTypeEnum::PointerType(refcount_t);
    let allocref_t = refcount_t.fn_type(&[arg_ty], false);

    m.add_function("__allocref_f", allocref_t, Some(Linkage::External))
}

fn build_deallocref_prototype<'a>(m: &Module<'a>, c: &'a Context) -> FunctionValue<'a> {
    let void = c.void_type();
    let int64 = c.i64_type();
    let refcount_t = int64.ptr_type(Default::default());
    let arg_ty = BasicMetadataTypeEnum::PointerType(refcount_t);
    let deallocref_t = void.fn_type(&[arg_ty], false);

    m.add_function("__deallocref_f", deallocref_t, Some(Linkage::External))
}

fn build_incref_prototype<'a>(m: &Module<'a>, c: &'a Context) -> FunctionValue<'a> {
    let void = c.void_type();
    let int64 = c.i64_type();
    let refcount_t = int64.ptr_type(Default::default());
    let arg_ty = BasicMetadataTypeEnum::PointerType(refcount_t);
    let incref_t = void.fn_type(&[arg_ty], false);

    m.add_function("__incref_f", incref_t, Some(Linkage::External))
}

fn build_decref_prototype<'a>(m: &Module<'a>, c: &'a Context) -> FunctionValue<'a> {
    let void = c.void_type();
    let int64 = c.i64_type();
    let refcount_t = int64.ptr_type(Default::default());
    let arg_ty = BasicMetadataTypeEnum::PointerType(refcount_t);
    let incref_t = void.fn_type(&[arg_ty], false);

    m.add_function("__decref_f", incref_t, Some(Linkage::External))
}

fn build_getref_prototype<'a>(m: &Module<'a>, c: &'a Context) -> FunctionValue<'a> {
    let int64 = c.i64_type();
    let refcount_t = int64.ptr_type(Default::default());
    let arg_ty = BasicMetadataTypeEnum::PointerType(refcount_t);
    let incref_t = int64.fn_type(&[arg_ty], false);

    m.add_function("__getref_f", incref_t, Some(Linkage::External))
}

#[derive(Clone)]
pub struct Refcounting<'a> {
    pub refcount_type: StructType<'a>,
    pub allocref_func: FunctionValue<'a>,
    pub deallocref_func: FunctionValue<'a>,
    pub incref_func: FunctionValue<'a>,
    pub getref_func: FunctionValue<'a>,
    pub decref_func: FunctionValue<'a>,
}

fn build_refcount_prototye_apis<'a>(m: &Module<'a>, c: &'a Context) -> Refcounting<'a> {
    let __refcount_t = build_refcount_type(c);
    let __allocref_f = build_allocref_prototype(m, c);
    let __deallocref_f = build_deallocref_prototype(m, c);
    let __incref_f = build_incref_prototype(m, c);
    let __getref_f = build_getref_prototype(m, c);
    let __decref_f = build_decref_prototype(m, c);

    Refcounting {
        refcount_type: __refcount_t,
        allocref_func: __allocref_f,
        deallocref_func: __deallocref_f,
        incref_func: __incref_f,
        getref_func: __getref_f,
        decref_func: __decref_f,
    }
}

pub fn build_refcount_apis<'a>(m: &Module<'a>, c: &'a Context) -> Refcounting<'a> {
    build_refcount_prototye_apis(m, c)
}

pub fn alloc_refcounted_type<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    ty: StructType<'a>,
) -> PointerValue<'a> {
    let metadata_ptr = iw.metadata.find_metadata_for_type(iw, ty).unwrap();
    let metadata_ptr = BasicMetadataValueEnum::PointerValue(metadata_ptr.as_pointer_value());

    let ptr = builder
        .build_call(iw.refcnt.allocref_func, &[metadata_ptr], "")
        .as_any_value_enum()
        .into_pointer_value();
    let ptr = builder.build_pointer_cast(ptr, ty.ptr_type(Default::default()), "");

    ptr
}

fn insert_incref_call<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: PointerValue<'a>,
) -> PointerValue<'a> {
    let incref_f = iw.refcnt.incref_func;
    let ptr = BasicMetadataValueEnum::PointerValue(val);
    builder.build_call(incref_f, &[ptr], "");
    val
}

pub fn insert_incref_if_refcounted<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: BasicValueEnum<'a>,
) -> BasicValueEnum<'a> {
    let tb = TypeBuilder::new(iw.clone());

    if tb.is_refcounted_basic_type(val.get_type()).is_some() {
        insert_incref_call(iw, builder, val.into_pointer_value());
    }

    val
}

fn insert_decref_call<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: PointerValue<'a>,
) -> PointerValue<'a> {
    let decref_f = iw.refcnt.decref_func;
    let ptr = BasicMetadataValueEnum::PointerValue(val);
    builder.build_call(decref_f, &[ptr], "");
    val
}

pub fn insert_decref_if_refcounted<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: BasicValueEnum<'a>,
) -> BasicValueEnum<'a> {
    let tb = TypeBuilder::new(iw.clone());

    if tb.is_refcounted_basic_type(val.get_type()).is_some() {
        insert_decref_call(iw, builder, val.into_pointer_value());
    }

    val
}

pub fn insert_decref_assume_refcounted<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: BasicValueEnum<'a>,
) -> BasicValueEnum<'a> {
    insert_decref_call(iw, builder, val.into_pointer_value());
    val
}

fn insert_getref_call<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: PointerValue<'a>,
) -> IntValue<'a> {
    let getref_f = iw.refcnt.getref_func;
    let ptr = BasicMetadataValueEnum::PointerValue(val);
    let v = builder.build_call(getref_f, &[ptr], "");
    return v.try_as_basic_value().unwrap_left().into_int_value();
}

pub fn insert_getref_if_refcounted<'a>(
    iw: &CompilerCore<'a>,
    builder: &Builder<'a>,
    val: BasicValueEnum<'a>,
) -> Option<IntValue<'a>> {
    let tb = TypeBuilder::new(iw.clone());

    if tb.is_refcounted_basic_type(val.get_type()).is_some() {
        return Some(insert_getref_call(iw, builder, val.into_pointer_value()));
    }

    None
}

pub fn find_sys_dealloc_for_type<'a>(
    iw: &CompilerCore<'a>,
    ty: StructType<'a>,
) -> FunctionValue<'a> {
    let name = mangle_special_method(
        ty,
        crate::mangler::SpecialMemberFunction::BuiltinDeallocator,
    );
    iw.module.get_function(&name).unwrap()
}

fn find_usr_dealloc_for_type<'a>(
    iw: &CompilerCore<'a>,
    ty: StructType<'a>,
) -> Option<FunctionValue<'a>> {
    let name = mangle_special_method(ty, crate::mangler::SpecialMemberFunction::UserDeallocator);
    iw.module.get_function(&name)
}

pub fn build_sys_dealloc<'a>(
    tb: &TypeBuilder<'a>,
    iw: &CompilerCore<'a>,
    ty: StructType<'a>,
    cdg_st: &Structure<'a>,
) -> FunctionValue<'a> {
    let this_type = iw.refcnt.refcount_type.ptr_type(Default::default());
    let func_type = iw
        .builtins
        .void
        .fn_type(&[BasicMetadataTypeEnum::PointerType(this_type)], false);
    let name = mangle_special_method(
        ty,
        crate::mangler::SpecialMemberFunction::BuiltinDeallocator,
    );
    let func = iw
        .module
        .add_function(&name, func_type, Some(Linkage::Internal));
    let builder = iw.context.create_builder();

    let decref_f = &iw.refcnt.decref_func;

    let entry = iw.context.append_basic_block(func, "entry");
    builder.position_at_end(entry);

    if cdg_st.ms == MemoryStrategy::ByReference {
        let do_free = iw.context.append_basic_block(func, "do_free");

        let arg0 = func.get_nth_param(0).unwrap().into_pointer_value();
        let arg0_retyped = builder.build_pointer_cast(arg0, ty.ptr_type(Default::default()), "");

        if let Some(usr_dealloc_f) = find_usr_dealloc_for_type(iw, ty) {
            builder.build_call(
                usr_dealloc_f,
                &[BasicMetadataValueEnum::PointerValue(arg0)],
                "",
            );
        }
        builder.build_unconditional_branch(do_free);

        builder.position_at_end(do_free);
        for i in 0..ty.get_field_types().len() {
            if let Some(field_ty) = ty.get_field_type_at_index(i as u32) {
                if tb.is_refcounted_basic_type(field_ty).is_some() {
                    if let Ok(field_gep) = builder.build_struct_gep(arg0_retyped, i as u32, "") {
                        let field_value = builder.build_load(field_gep, "");
                        builder.build_store(field_gep, field_ty.const_zero());
                        let field_value = builder.build_pointer_cast(
                            field_value.into_pointer_value(),
                            iw.refcnt.refcount_type.ptr_type(Default::default()),
                            "",
                        );
                        builder.build_call(
                            *decref_f,
                            &[BasicMetadataValueEnum::PointerValue(field_value)],
                            "",
                        );
                    }
                }
            }
        }

        let arg0_bmve = BasicMetadataValueEnum::PointerValue(arg0);
        builder.build_call(iw.refcnt.deallocref_func, &[arg0_bmve], "");
    }
    builder.build_return(None);

    func
}
