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
        IntType, StructType,
    },
    values::{BasicValueEnum, FunctionValue, IntValue},
};

use crate::{
    ast::{
        DeallocDecl, FieldDecl, FunctionArgument, FunctionDecl, FunctionDefinition,
        FunctionTypeDescriptor, ImplDecl, InitDecl, ProperStructDecl, TokenSpan, TypeDescriptor,
    },
    bom::strct::{ImplBomEntry, StructBomEntry},
    codegen::{
        self,
        structure::{MemoryStrategy, Method, Structure},
    },
    err::{CompilerError, CompilerWarning, Error},
    iw::CompilerCore,
    mangler::mangle_special_method,
};

use super::{
    func::{FunctionBuilder, FunctionBuilderOptions},
    refcount::build_dealloc,
    scope::Scope,
};

pub struct TypeBuilder<'a> {
    iw: CompilerCore<'a>,
}

impl<'a> TypeBuilder<'a> {
    pub fn new(iw: CompilerCore<'a>) -> Self {
        Self { iw }
    }
}

impl<'a> TypeBuilder<'a> {
    pub fn alias(
        &self,
        scope: &Scope<'a>,
        name: &str,
        ty: &TypeDescriptor,
    ) -> Option<BasicTypeEnum<'a>> {
        if let Some(ty) = self.llvm_type_by_descriptor(scope, ty) {
            scope.insert_alias(name, ty, true);
            Some(ty)
        } else {
            None
        }
    }

    pub fn is_tuple_type(st: StructType) -> bool {
        st.get_name().is_none()
    }

    pub fn is_valtype_with_refcount_field(&self, st: StructType<'a>) -> bool {
        if self.is_value_type(st) || TypeBuilder::is_tuple_type(st) {
            for fd in st.get_field_types() {
                if self.is_refcounted_basic_type(fd).is_some() {
                    return true;
                }
            }
            false
        } else {
            false
        }
    }

    pub fn any_type_from_basic(ty: BasicTypeEnum) -> AnyTypeEnum {
        match ty {
            BasicTypeEnum::ArrayType(at) => AnyTypeEnum::ArrayType(at),
            BasicTypeEnum::FloatType(ft) => AnyTypeEnum::FloatType(ft),
            BasicTypeEnum::IntType(it) => AnyTypeEnum::IntType(it),
            BasicTypeEnum::PointerType(pt) => AnyTypeEnum::PointerType(pt),
            BasicTypeEnum::StructType(st) => AnyTypeEnum::StructType(st),
            BasicTypeEnum::VectorType(vt) => AnyTypeEnum::VectorType(vt),
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
            BasicTypeEnum::IntType(it) => {
                let n = format!("int{}", it.get_bit_width());
                Some(TypeDescriptor::Name(n))
            }
            BasicTypeEnum::FloatType(ft) => {
                let is_f64 = ft.get_context().f64_type() == ft;
                if is_f64 {
                    return Some(TypeDescriptor::Name(String::from("float64")));
                }
                let is_f32 = ft.get_context().f32_type() == ft;
                if is_f32 {
                    return Some(TypeDescriptor::Name(String::from("float32")));
                }
                None
            }
            BasicTypeEnum::PointerType(pt) => {
                let pointee = pt.get_element_type();
                match pointee {
                    AnyTypeEnum::ArrayType(_)
                    | AnyTypeEnum::FloatType(_)
                    | AnyTypeEnum::IntType(_)
                    | AnyTypeEnum::PointerType(_)
                    | AnyTypeEnum::StructType(_)
                    | AnyTypeEnum::VectorType(_) => TypeBuilder::descriptor_by_llvm_type(
                        BasicTypeEnum::try_from(pointee).unwrap(),
                    ),
                    AnyTypeEnum::FunctionType(ft) => TypeBuilder::descriptor_for_function_type(ft),
                    AnyTypeEnum::VoidType(_) => panic!("unexpected void type"),
                }
            }
            BasicTypeEnum::StructType(st) => {
                if let Some(n) = st.get_name() {
                    let n = n.to_str().unwrap().to_owned();
                    Some(TypeDescriptor::Name(n))
                } else {
                    let fts: Vec<Option<TypeDescriptor>> = st
                        .get_field_types()
                        .iter()
                        .map(|bt| TypeBuilder::descriptor_by_llvm_type(*bt))
                        .collect();
                    if fts.iter().any(|td| td.is_none()) {
                        return None;
                    }
                    let fts: Vec<TypeDescriptor> =
                        fts.iter().map(|ft| ft.clone().unwrap()).collect();
                    Some(TypeDescriptor::Tuple(fts))
                }
            }
            BasicTypeEnum::VectorType(_) => None,
        }
    }

    pub fn llvm_type_by_descriptor(
        &self,
        scope: &Scope<'a>,
        td: &TypeDescriptor,
    ) -> Option<BasicTypeEnum<'a>> {
        match td {
            TypeDescriptor::Name(name) => {
                if let Some(ty) = scope.find_alias(name, true) {
                    return Some(ty);
                }

                return self.iw.structs.borrow().get(name).map(|ty| ty.var_ty);
            }
            TypeDescriptor::Pointer(ptr) => {
                return self
                    .llvm_type_by_descriptor(scope, ptr.as_ref())
                    .map(|pointee| {
                        BasicTypeEnum::PointerType(pointee.ptr_type(Default::default()))
                    });
            }
            TypeDescriptor::Array(ty, sz) => {
                return self
                    .llvm_type_by_descriptor(scope, ty.as_ref())
                    .map(|el_ty| BasicTypeEnum::ArrayType(el_ty.array_type(*sz as u32)));
            }
            TypeDescriptor::Function(..) => self
                .function_type_for_descriptor(scope, td)
                .map(|ft| BasicTypeEnum::PointerType(ft.ptr_type(Default::default()))),
            TypeDescriptor::Tuple(at) => {
                let eltys: Vec<Option<BasicTypeEnum<'a>>> = at
                    .iter()
                    .map(|td| self.llvm_type_by_descriptor(scope, td))
                    .collect();
                if eltys.iter().any(|at| at.is_none()) {
                    return None;
                }
                let eltys: Vec<BasicTypeEnum<'a>> = eltys.iter().map(|x| x.unwrap()).collect();
                let raw_struct = self.iw.context.struct_type(&eltys, false);
                Some(BasicTypeEnum::StructType(raw_struct))
            }
        }
    }

    pub fn is_boolean_basic(ty: BasicTypeEnum<'a>) -> bool {
        if ty.is_int_type() {
            TypeBuilder::is_boolean_int(ty.into_int_type())
        } else {
            false
        }
    }

    pub fn is_boolean_any(ty: AnyTypeEnum<'a>) -> bool {
        if ty.is_int_type() {
            TypeBuilder::is_boolean_int(ty.into_int_type())
        } else {
            false
        }
    }

    pub fn is_boolean_int(ty: IntType<'a>) -> bool {
        ty.get_bit_width() == 1
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

    pub fn alignof(&self, ty: BasicTypeEnum<'a>) -> IntValue<'a> {
        match ty {
            BasicTypeEnum::ArrayType(at) => at.get_alignment(),
            BasicTypeEnum::FloatType(ft) => ft.get_alignment(),
            BasicTypeEnum::IntType(it) => it.get_alignment(),
            BasicTypeEnum::PointerType(pt) => pt.get_alignment(),
            BasicTypeEnum::StructType(st) => st.get_alignment(),
            BasicTypeEnum::VectorType(vt) => vt.get_alignment(),
        }
    }

    pub fn descriptor_for_function_type(ty: FunctionType) -> Option<TypeDescriptor> {
        let return_type = if ty.get_return_type().is_none() {
            None
        } else {
            TypeBuilder::descriptor_by_llvm_type(ty.get_return_type().unwrap()).map(Box::new)
        };
        let arg_types: Vec<Option<TypeDescriptor>> = ty
            .get_param_types()
            .iter()
            .map(|at| TypeBuilder::descriptor_by_llvm_type(*at))
            .collect();
        if arg_types.iter().any(|at| at.is_none()) {
            return None;
        }
        let arg_types: Vec<TypeDescriptor> = arg_types.iter().map(|x| x.clone().unwrap()).collect();
        let vararg = ty.is_var_arg();

        let ftd = FunctionTypeDescriptor::new(arg_types, return_type, vararg);
        Some(TypeDescriptor::Function(ftd))
    }

    pub fn function_type_for_descriptor(
        &self,
        scope: &Scope<'a>,
        td: &TypeDescriptor,
    ) -> Option<FunctionType<'a>> {
        if let TypeDescriptor::Function(ftd) = td {
            let map_args: Vec<Option<BasicTypeEnum>> = ftd
                .args
                .iter()
                .map(|td| self.llvm_type_by_descriptor(scope, td))
                .collect();
            if map_args.iter().any(|at| at.is_none()) {
                return None;
            }
            let param_types: Vec<BasicMetadataTypeEnum> = map_args
                .iter()
                .map(|at| BasicMetadataTypeEnum::try_from(at.unwrap()).unwrap())
                .collect();

            if ftd.ret.is_none() {
                Some(self.iw.builtins.void.fn_type(&param_types, ftd.vararg))
            } else {
                self.llvm_type_by_descriptor(scope, ftd.ret.as_ref().unwrap())
                    .map(|ret| ret.fn_type(&param_types, ftd.vararg))
            }
        } else {
            None
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

    pub fn find_init_for_type(
        &self,
        scope: &Scope<'a>,
        this_ty: StructType<'a>,
    ) -> Option<FunctionValue<'a>> {
        let full_name =
            mangle_special_method(this_ty, crate::mangler::SpecialMemberFunction::Initializer);
        scope.find_function(&full_name, true)
    }

    fn build_init(
        &self,
        scope: &Scope<'a>,
        this_ty: StructType<'a>,
        init: &InitDecl,
        export: bool,
    ) -> Option<FunctionValue<'a>> {
        let ty = TypeDescriptor::Name(this_ty.get_name().unwrap().to_str().unwrap().to_owned());
        let mut real_args = vec![FunctionArgument {
            loc: init.loc,
            name: String::from("self"),
            ty,
            rw: false,
            explicit_rw: false,
        }];
        init.args.iter().for_each(|a| real_args.push(a.clone()));
        let full_name =
            mangle_special_method(this_ty, crate::mangler::SpecialMemberFunction::Initializer);

        let init_arg_types: Vec<TypeDescriptor> =
            real_args.iter().map(|arg| arg.ty.clone()).collect();
        let ftd = FunctionTypeDescriptor::new(init_arg_types, None, false);
        let fn_type = TypeDescriptor::Function(ftd);

        let func_def = FunctionDefinition {
            decl: FunctionDecl {
                loc: init.loc,
                name: full_name,
                args: real_args,
                ty: fn_type,
            },
            body: init.body.clone(),
            export: false,
        };

        let fb = FunctionBuilder::new(self.iw.clone());
        let opts = FunctionBuilderOptions::default()
            .extrn(false)
            .global(true)
            .mangle(false)
            .export(export)
            .commit();
        fb.compile(scope, &func_def, opts)
    }

    fn build_usr_dealloc(
        &self,
        scope: &Scope<'a>,
        this_ty: StructType<'a>,
        dealloc: &DeallocDecl,
        export: bool,
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

        let ftd = FunctionTypeDescriptor::new(vec![ty], None, false);
        let fn_type = TypeDescriptor::Function(ftd);

        let func_def = FunctionDefinition {
            decl: FunctionDecl {
                loc: dealloc.loc,
                name: full_name,
                args: real_args,
                ty: fn_type,
            },
            body: dealloc.body.clone(),
            export: false,
        };

        let fb = FunctionBuilder::new(self.iw.clone());
        let opts = FunctionBuilderOptions::default()
            .extrn(false)
            .global(true)
            .mangle(false)
            .export(export)
            .commit();
        fb.compile(scope, &func_def, opts)
    }

    pub fn build_structure_from_bom(
        &self,
        _scope: &Scope<'a>,
        sd: &StructBomEntry,
    ) -> Option<StructType<'a>> {
        let ms = sd.ms;
        let is_rc = sd.ms == MemoryStrategy::ByReference;
        let is_val = sd.ms == MemoryStrategy::ByValue;

        // if is_val && sd.init.is_some() {
        //     self.iw.error(CompilerError::new(
        //         sd.init.as_ref().unwrap().loc,
        //         Error::InitDisallowedInValueTypes,
        //     ));
        //     return None;
        // }

        let st_ty = self.iw.context.opaque_struct_type(&sd.name);

        let var_ty = if is_rc {
            BasicTypeEnum::PointerType(st_ty.ptr_type(Default::default()))
        } else {
            BasicTypeEnum::StructType(st_ty)
        };

        let cdg_st = codegen::structure::Structure {
            name: sd.name.clone(),
            str_ty: st_ty,
            var_ty,
            ms,
            fields: Default::default(),
            methods: Default::default(),
            export: false, // no need to re-export?
        };
        self.iw.add_struct(&cdg_st);

        let mut fields: Vec<BasicTypeEnum> = vec![];

        for fd in &sd.fields {
            if let Some(field_ty) =
                self.llvm_type_by_descriptor(&self.iw.globals, &fd.underlying_type)
            {
                if is_val && field_ty == BasicTypeEnum::StructType(st_ty) {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        TokenSpan::origin(),
                        Error::RecursiveTypeForbidden(fd.name.clone()),
                    ));
                    return None;
                }

                if is_val && self.is_refcounted_basic_type(field_ty).is_some() {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        TokenSpan::origin(),
                        Error::RefTypeInValTypeForbidden,
                    ));
                    return None;
                }

                fields.push(field_ty);
                cdg_st.fields.borrow_mut().push(codegen::structure::Field {
                    name: fd.name.clone(),
                    ty: field_ty,
                });
            } else {
                self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                    TokenSpan::origin(),
                    Error::TypeNotFound(fd.underlying_type.clone()),
                ));
                return None;
            }
        }

        st_ty.set_body(&fields, false);
        build_dealloc(self, &self.iw, st_ty);

        // if let Some(init) = &sd.init {
        //     if self.build_init(scope, st_ty, init).is_none() {
        //         self.iw
        //             .error(CompilerError::new(init.loc, Error::InvalidExpression));
        //         return None;
        //     }
        // }

        // if let Some(dealloc) = &sd.dealloc {
        //     if self.build_usr_dealloc(scope, st_ty, dealloc).is_none() {
        //         self.iw
        //             .error(CompilerError::new(dealloc.loc, Error::InvalidExpression));
        //         return None;
        //     }
        // }

        Some(st_ty)
    }

    pub fn build_structure_from_decl(
        &self,
        scope: &Scope<'a>,
        sd: &ProperStructDecl,
    ) -> Option<StructType> {
        let ms = sd.ms;
        let is_rc = sd.ms == MemoryStrategy::ByReference;
        let is_val = sd.ms == MemoryStrategy::ByValue;

        if is_val && sd.init.is_some() {
            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
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
            name: sd.name.clone(),
            str_ty: st_ty,
            var_ty,
            ms,
            fields: Default::default(),
            methods: Default::default(),
            export: sd.export,
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
                    name: "__sys_dealloc".to_owned(),
                    ty: TypeDescriptor::Name("int64".to_owned()),
                },
            );
            sd_fields.insert(
                2,
                FieldDecl {
                    loc: sd.loc,
                    name: "__usr_dealloc".to_owned(),
                    ty: TypeDescriptor::Name("int64".to_owned()),
                },
            );
        }

        let mut fields: Vec<BasicTypeEnum> = vec![];

        for fd in &sd_fields {
            if let Some(field_ty) = self.llvm_type_by_descriptor(&self.iw.globals, &fd.ty) {
                if is_val && field_ty == BasicTypeEnum::StructType(st_ty) {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        fd.loc,
                        Error::RecursiveTypeForbidden(fd.name.clone()),
                    ));
                    return None;
                }

                if is_val && self.is_refcounted_basic_type(field_ty).is_some() {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(fd.loc, Error::RefTypeInValTypeForbidden));
                    return None;
                }

                fields.push(field_ty);
                cdg_st.fields.borrow_mut().push(codegen::structure::Field {
                    name: fd.name.clone(),
                    ty: field_ty,
                });
            } else {
                self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                    fd.loc,
                    Error::TypeNotFound(fd.ty.clone()),
                ));
                return None;
            }
        }

        st_ty.set_body(&fields, false);
        build_dealloc(self, &self.iw, st_ty);

        if let Some(init) = &sd.init {
            if self.build_init(scope, st_ty, init, sd.export).is_none() {
                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(init.loc, Error::InvalidExpression));
                return None;
            }
        }

        if let Some(dealloc) = &sd.dealloc {
            if self
                .build_usr_dealloc(scope, st_ty, dealloc, sd.export)
                .is_none()
            {
                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(dealloc.loc, Error::InvalidExpression));
                return None;
            }
        }

        Some(st_ty)
    }

    pub fn struct_by_name(&self, st: StructType) -> Option<Structure<'a>> {
        if TypeBuilder::is_tuple_type(st) {
            None
        } else {
            let name = st.get_name().unwrap().to_str().unwrap();
            self.iw.structs.borrow().get(name).cloned()
        }
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

    pub fn is_val_or_ref_basic_type(&self, ty: BasicTypeEnum<'a>) -> Option<StructType<'a>> {
        if let Some(st) = self.is_refcounted_basic_type(ty) {
            Some(st)
        } else {
            self.is_value_basic_type(ty)
        }
    }

    pub fn is_val_or_ref_any_type(&self, ty: AnyTypeEnum<'a>) -> Option<StructType<'a>> {
        if let Some(st) = self.is_refcounted_any_type(ty) {
            Some(st)
        } else {
            self.is_value_any_type(ty)
        }
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

    pub fn build_impl(&self, scope: &Scope<'a>, sd: &Structure<'a>, id: &ImplDecl) {
        let mut bom_entry = ImplBomEntry::new(sd);
        let fb = FunctionBuilder::new(self.iw.clone());
        let mut decls: Vec<FunctionDecl> = vec![];
        let export = if id.export && !sd.export {
            self.iw
                .diagnostics
                .borrow_mut()
                .warning(CompilerWarning::new(
                    id.loc,
                    crate::err::Warning::ExportImplIgnored,
                ));
            false
        } else {
            sd.export && id.export
        };
        for method in &id.methods {
            let decl = fb.declare_method(scope, &method.imp, sd, export);
            if let Some(func) = decl.1 {
                let new_method = Method {
                    name: method.imp.decl.name.clone(),
                    func,
                };
                bom_entry.add_method(&new_method);
                sd.methods.borrow_mut().push(new_method);
                decls.push(decl.0);
            } else {
                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(method.loc, Error::InvalidExpression));
                return;
            }
        }
        for (id, method) in id.methods.iter().enumerate() {
            let decl = decls.get(id).unwrap();
            fb.define_method(scope, &method.imp, decl);
        }
        if export {
            self.iw.bom.borrow_mut().impls.push(bom_entry);
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
            let sign_flag = !TypeBuilder::is_boolean_int(st);
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
