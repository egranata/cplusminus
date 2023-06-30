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
    types::{
        AnyTypeEnum, ArrayType, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType,
        StructType,
    },
    values::{BasicValueEnum, FunctionValue, IntValue},
};

use crate::{
    ast::{
        DeallocDecl, FieldDecl, FunctionArgument, FunctionDecl, FunctionDefinition, ImplDecl,
        InitDecl, ProperStructDecl, TypeDescriptor,
    },
    codegen::{
        self,
        structure::{MemoryStrategy, Method, Structure},
    },
    err::{CompilerError, Error},
    iw::CompilerCore,
    mangler::mangle_special_method,
};

use super::{func::FunctionBuilder, refcount::build_dealloc};

pub struct TypeBuilder<'a> {
    iw: CompilerCore<'a>,
}

impl<'a> TypeBuilder<'a> {
    pub fn new(iw: CompilerCore<'a>) -> Self {
        Self { iw }
    }
}

impl<'a> TypeBuilder<'a> {
    pub fn alias(&self, name: &str, ty: &TypeDescriptor) -> Option<BasicTypeEnum<'a>> {
        if let Some(ty) = self.llvm_type_by_descriptor(ty) {
            self.iw.types.borrow_mut().insert(name.to_string(), ty);
            Some(ty)
        } else {
            None
        }
    }

    pub fn undef_for_type(ty: BasicTypeEnum) -> BasicValueEnum {
        match ty {
            BasicTypeEnum::ArrayType(at) => BasicValueEnum::from(at.get_undef()),
            BasicTypeEnum::FloatType(ft) => BasicValueEnum::from(ft.get_undef()),
            BasicTypeEnum::IntType(it) => BasicValueEnum::from(it.get_undef()),
            BasicTypeEnum::PointerType(pt) => BasicValueEnum::from(pt.get_undef()),
            BasicTypeEnum::StructType(st) => BasicValueEnum::from(st.get_undef()),
            BasicTypeEnum::VectorType(vt) => BasicValueEnum::from(vt.get_undef()),
        }
    }

    pub fn zero_for_type(ty: BasicTypeEnum) -> BasicValueEnum {
        ty.const_zero()
    }

    pub fn descriptor_by_llvm_type(ty: BasicTypeEnum) -> Option<TypeDescriptor> {
        match ty {
            BasicTypeEnum::ArrayType(at) => {
                if let Some(td) = TypeBuilder::descriptor_by_llvm_type(at.get_element_type()) {
                    let n = at.len();
                    return Some(TypeDescriptor::Array(Box::new(td), n as usize));
                }
                None
            }
            BasicTypeEnum::FloatType(_) => None,
            BasicTypeEnum::IntType(it) => {
                let n = format!("int{}", it.get_bit_width());
                Some(TypeDescriptor::Name(n))
            }
            BasicTypeEnum::PointerType(pt) => {
                if let Ok(pointee) = BasicTypeEnum::try_from(pt.get_element_type()) {
                    if let Some(td) = TypeBuilder::descriptor_by_llvm_type(pointee) {
                        return Some(TypeDescriptor::Pointer(Box::new(td)));
                    }
                }
                None
            }
            BasicTypeEnum::StructType(st) => {
                let n = st.get_name().unwrap().to_str().unwrap().to_owned();
                Some(TypeDescriptor::Name(n))
            }
            BasicTypeEnum::VectorType(_) => None,
        }
    }

    pub fn llvm_type_by_descriptor(&self, td: &TypeDescriptor) -> Option<BasicTypeEnum<'a>> {
        match td {
            TypeDescriptor::Name(name) => {
                if let Some(ty) = self.iw.types.borrow().get(name) {
                    return Some(*ty);
                }

                return self.iw.structs.borrow().get(name).map(|ty| ty.var_ty);
            }
            TypeDescriptor::Pointer(ptr) => {
                return self.llvm_type_by_descriptor(ptr.as_ref()).map(|pointee| {
                    BasicTypeEnum::PointerType(pointee.ptr_type(Default::default()))
                });
            }
            TypeDescriptor::Array(ty, sz) => {
                return self
                    .llvm_type_by_descriptor(ty.as_ref())
                    .map(|el_ty| BasicTypeEnum::ArrayType(el_ty.array_type(*sz as u32)));
            }
            TypeDescriptor::Function(args, ret, is_var_args) => {
                if let Some(ret) = self.llvm_type_by_descriptor(ret.as_ref()) {
                    let map_args: Vec<Option<BasicTypeEnum>> = args
                        .iter()
                        .map(|td| self.llvm_type_by_descriptor(td))
                        .collect();
                    if map_args.iter().any(|at| at.is_none()) {
                        return None;
                    }
                    let param_types: Vec<BasicMetadataTypeEnum> = map_args
                        .iter()
                        .map(|at| BasicMetadataTypeEnum::try_from(at.unwrap()).unwrap())
                        .collect();
                    return Some(BasicTypeEnum::PointerType(
                        ret.fn_type(&param_types, *is_var_args)
                            .ptr_type(Default::default()),
                    ));
                } else {
                    None
                }
            }
        }
    }

    pub fn is_boolean(&self, ty: BasicTypeEnum<'a>) -> bool {
        if ty.is_int_type() {
            ty.into_int_type().get_bit_width() == 1
        } else {
            false
        }
    }

    pub fn is_same_type(&self, lhs: BasicTypeEnum<'a>, rhs: AnyTypeEnum<'a>) -> bool {
        BasicTypeEnum::try_from(rhs).map_or(false, |bhs| bhs == lhs)
    }

    pub fn sizeof(&self, ty: BasicTypeEnum<'a>) -> IntValue<'a> {
        match ty {
            BasicTypeEnum::ArrayType(at) => at.size_of().unwrap(),
            BasicTypeEnum::FloatType(ft) => ft.size_of(),
            BasicTypeEnum::IntType(it) => it.size_of(),
            BasicTypeEnum::PointerType(pt) => pt.size_of(),
            BasicTypeEnum::StructType(st) => st.size_of().unwrap(),
            BasicTypeEnum::VectorType(vt) => vt.size_of().unwrap(),
        }
    }

    pub fn llvm_function_type(
        &self,
        args: &[BasicTypeEnum<'a>],
        ret: Option<BasicTypeEnum<'a>>,
        va: bool,
    ) -> FunctionType<'a> {
        let args: Vec<BasicMetadataTypeEnum> = args.iter().map(|arg| (*arg).into()).collect();
        if let Some(ret) = ret {
            match ret {
                BasicTypeEnum::ArrayType(at) => at.fn_type(&args, va),
                BasicTypeEnum::FloatType(ft) => ft.fn_type(&args, va),
                BasicTypeEnum::IntType(it) => it.fn_type(&args, va),
                BasicTypeEnum::PointerType(pt) => pt.fn_type(&args, va),
                BasicTypeEnum::StructType(st) => st.fn_type(&args, va),
                BasicTypeEnum::VectorType(vt) => vt.fn_type(&args, va),
            }
        } else {
            self.iw.context.void_type().fn_type(&args, va)
        }
    }

    pub fn llvm_array_type(&self, el_ty: BasicTypeEnum<'a>, size: u32) -> ArrayType<'a> {
        match el_ty {
            BasicTypeEnum::ArrayType(at) => at.array_type(size),
            BasicTypeEnum::FloatType(ft) => ft.array_type(size),
            BasicTypeEnum::IntType(it) => it.array_type(size),
            BasicTypeEnum::PointerType(pt) => pt.array_type(size),
            BasicTypeEnum::StructType(st) => st.array_type(size),
            BasicTypeEnum::VectorType(vt) => vt.array_type(size),
        }
    }

    fn build_init(&self, this_ty: StructType<'a>, init: &InitDecl) -> Option<FunctionValue<'a>> {
        let ty = TypeDescriptor::Name(this_ty.get_name().unwrap().to_str().unwrap().to_owned());
        let mut real_args = vec![FunctionArgument {
            loc: init.loc,
            name: String::from("self"),
            ty: ty.clone(),
            rw: false,
            explicit_rw: false,
        }];
        init.args.iter().for_each(|a| real_args.push(a.clone()));
        let full_name =
            mangle_special_method(this_ty, crate::mangler::SpecialMemberFunction::Initializer);

        let func_def = FunctionDefinition {
            decl: FunctionDecl {
                loc: init.loc,
                name: full_name,
                args: real_args,
                vararg: false,
                ty,
            },
            body: init.body.clone(),
        };

        let fb = FunctionBuilder::new(self.iw.clone());
        fb.compile(&func_def)
    }

    fn build_usr_dealloc(
        &self,
        this_ty: StructType<'a>,
        dealloc: &DeallocDecl,
    ) -> Option<FunctionValue<'a>> {
        let ty = TypeDescriptor::Name(this_ty.get_name().unwrap().to_str().unwrap().to_owned());
        let real_args = vec![FunctionArgument {
            loc: dealloc.loc,
            name: String::from("self"),
            ty: ty.clone(),
            rw: false,
            explicit_rw: false,
        }];
        let full_name = mangle_special_method(
            this_ty,
            crate::mangler::SpecialMemberFunction::UserDeallocator,
        );

        let func_def = FunctionDefinition {
            decl: FunctionDecl {
                loc: dealloc.loc,
                name: full_name,
                args: real_args,
                vararg: false,
                ty,
            },
            body: dealloc.body.clone(),
        };

        let fb = FunctionBuilder::new(self.iw.clone());
        fb.compile(&func_def)
    }

    pub fn build_structure(&self, sd: &ProperStructDecl) -> Option<StructType> {
        let ms = sd.ms;
        let is_rc = sd.ms == MemoryStrategy::ByReference;
        let is_val = sd.ms == MemoryStrategy::ByValue;

        if is_val && sd.init.is_some() {
            self.iw.error(CompilerError::new(
                sd.init.as_ref().unwrap().loc,
                Error::InitDisallowedInValueTypes,
            ));
            return None;
        }

        let st_ty = self.iw.context.opaque_struct_type(&sd.name);

        let var_ty = if is_rc {
            BasicTypeEnum::PointerType(st_ty.ptr_type(Default::default()))
        } else {
            BasicTypeEnum::StructType(st_ty)
        };

        let cdg_st = codegen::structure::Structure {
            decl: sd.clone(),
            str_ty: st_ty,
            var_ty,
            ms,
            implementations: Default::default(),
            fields: Default::default(),
            methods: Default::default(),
            init: Default::default(),
            usr_dealloc: Default::default(),
            sys_dealloc: Default::default(),
        };
        self.iw.add_struct(&cdg_st);

        let mut sd_fields = sd.fields.clone();
        if is_rc {
            sd_fields.insert(
                0,
                FieldDecl {
                    loc: sd.loc,
                    name: "__rc".to_owned(),
                    ty: TypeDescriptor::Name("int64".to_owned()),
                },
            );
            sd_fields.insert(
                1,
                FieldDecl {
                    loc: sd.loc,
                    name: "__dealloc".to_owned(),
                    ty: TypeDescriptor::Name("int64".to_owned()),
                },
            );
        }

        let mut fields: Vec<BasicTypeEnum> = vec![];

        for fd in &sd_fields {
            if let Some(field_ty) = self.llvm_type_by_descriptor(&fd.ty) {
                if is_val && field_ty == BasicTypeEnum::StructType(st_ty) {
                    self.iw.error(CompilerError::new(
                        fd.loc,
                        Error::RecursiveTypeForbidden(fd.name.clone()),
                    ));
                    return None;
                }

                if is_val && self.is_refcounted_basic_type(field_ty).is_some() {
                    self.iw
                        .error(CompilerError::new(fd.loc, Error::RefTypeInValTypeForbidden));
                    return None;
                }

                fields.push(field_ty);
                cdg_st.fields.borrow_mut().push(codegen::structure::Field {
                    decl: fd.clone(),
                    ty: field_ty,
                });
            } else {
                self.iw.error(CompilerError::new(
                    fd.loc,
                    Error::TypeNotFound(fd.ty.clone()),
                ));
                return None;
            }
        }

        st_ty.set_body(&fields, false);

        if is_rc {
            let dealloc_f = build_dealloc(self, &self.iw, st_ty);
            let _ = cdg_st.sys_dealloc.set(dealloc_f);
        }

        if let Some(init) = &sd.init {
            if let Some(init_f) = self.build_init(st_ty, init) {
                let _ = cdg_st.init.set(init_f);
            } else {
                self.iw
                    .error(CompilerError::new(init.loc, Error::InvalidExpression));
                return None;
            }
        }

        if let Some(dealloc) = &sd.dealloc {
            if let Some(dealloc_f) = self.build_usr_dealloc(st_ty, dealloc) {
                let _ = cdg_st.init.set(dealloc_f);
            } else {
                self.iw
                    .error(CompilerError::new(dealloc.loc, Error::InvalidExpression));
                return None;
            }
        }

        Some(st_ty)
    }

    pub fn struct_by_name(&self, st: StructType) -> Option<Structure<'a>> {
        let name = st.get_name().unwrap().to_str().unwrap();
        return self.iw.structs.borrow().get(name).cloned();
    }

    fn is_refcounted_type(&self, sty: StructType<'a>) -> bool {
        if let Some(struc) = self.struct_by_name(sty) {
            if struc.ms == MemoryStrategy::ByReference {
                return true;
            }
        }

        false
    }

    fn is_value_type(&self, sty: StructType<'a>) -> bool {
        if let Some(struc) = self.struct_by_name(sty) {
            if struc.ms == MemoryStrategy::ByValue {
                return true;
            }
        }

        false
    }

    pub fn is_refcounted_any_type(&self, ty: AnyTypeEnum<'a>) -> Option<StructType<'a>> {
        if let AnyTypeEnum::PointerType(pty) = ty {
            if let AnyTypeEnum::StructType(sty) = pty.get_element_type() {
                if self.is_refcounted_type(sty) {
                    return Some(sty);
                }
            }
        }

        None
    }

    pub fn is_refcounted_basic_type(&self, ty: BasicTypeEnum<'a>) -> Option<StructType<'a>> {
        if let BasicTypeEnum::PointerType(pty) = ty {
            if let AnyTypeEnum::StructType(sty) = pty.get_element_type() {
                if self.is_refcounted_type(sty) {
                    return Some(sty);
                }
            }
        }

        None
    }

    pub fn is_value_any_type(&self, ty: AnyTypeEnum<'a>) -> Option<StructType<'a>> {
        if let AnyTypeEnum::StructType(sty) = ty {
            if self.is_value_type(sty) {
                return Some(sty);
            }
        }

        if let AnyTypeEnum::PointerType(ptr) = ty {
            if let AnyTypeEnum::StructType(sty) = ptr.get_element_type() {
                if self.is_value_type(sty) {
                    return Some(sty);
                }
            }
        }

        None
    }

    pub fn is_value_basic_type(&self, ty: BasicTypeEnum<'a>) -> Option<StructType<'a>> {
        if let BasicTypeEnum::StructType(sty) = ty {
            if self.is_value_type(sty) {
                return Some(sty);
            }
        }

        if let BasicTypeEnum::PointerType(ptr) = ty {
            if let AnyTypeEnum::StructType(sty) = ptr.get_element_type() {
                if self.is_value_type(sty) {
                    return Some(sty);
                }
            }
        }

        None
    }

    pub fn build_impl(&self, sd: &Structure<'a>, id: &ImplDecl) {
        sd.implementations.borrow_mut().push(id.clone());

        let fb = FunctionBuilder::new(self.iw.clone());
        for method in &id.methods {
            let uf = fb.as_method(&method.imp, &sd.decl);
            fb.declare(&uf.decl, false);
            let func = fb.build(&uf).unwrap();
            let new_method = Method {
                decl: method.clone(),
                func,
            };
            sd.methods.borrow_mut().push(new_method);
        }
    }

    pub fn build_cast(
        &self,
        builder: &Builder<'a>,
        expr: BasicValueEnum<'a>,
        ty: BasicTypeEnum<'a>,
    ) -> Option<BasicValueEnum<'a>> {
        use BasicTypeEnum::{IntType, PointerType};
        use BasicValueEnum::{IntValue, PointerValue};

        let expr_ty = expr.get_type();
        if expr_ty == ty {
            return Some(expr);
        }

        if let (IntType(st), IntType(dest_int)) = (expr_ty, ty) {
            let sign_flag = st.get_bit_width() != 1;
            return Some(IntValue(builder.build_int_cast_sign_flag(
                expr.into_int_value(),
                dest_int,
                sign_flag,
                "",
            )));
        }

        if let (PointerType(_), IntType(dest_int)) = (expr_ty, ty) {
            return Some(IntValue(builder.build_ptr_to_int(
                expr.into_pointer_value(),
                dest_int,
                "",
            )));
        }

        if let (IntType(_), PointerType(dest_ptr)) = (expr_ty, ty) {
            return Some(PointerValue(builder.build_int_to_ptr(
                expr.into_int_value(),
                dest_ptr,
                "",
            )));
        }

        if let (PointerType(_), PointerType(dest_ptr)) = (expr_ty, ty) {
            return Some(PointerValue(builder.build_pointer_cast(
                expr.into_pointer_value(),
                dest_ptr,
                "",
            )));
        }

        None
    }
}
