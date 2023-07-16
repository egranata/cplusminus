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

use inkwell::{builder::Builder, types::BasicTypeEnum, values::PointerValue};

use crate::{
    ast::{FunctionDefinition, Lvalue},
    err::Error,
    iw::CompilerCore,
};

use super::{
    expr::ExpressionBuilder,
    func::FunctionExitData,
    scope::{Scope, VarInfo},
    ty::TypeBuilder,
};

pub struct LvalueBuilder<'a, 'b> {
    iw: CompilerCore<'a>,
    exit: &'b FunctionExitData<'a>,
}

pub struct ResolvedLvalue<'a> {
    pub ptr: PointerValue<'a>,
    pub rw: bool,
    pub var: Option<VarInfo<'a>>,
}

impl<'a> ResolvedLvalue<'a> {
    pub fn mark_written(&self) {
        if let Some(vi) = &self.var {
            *vi.written.borrow_mut() = true
        }
    }
}

impl<'a, 'b> LvalueBuilder<'a, 'b> {
    pub fn new(iw: CompilerCore<'a>, exit: &'b FunctionExitData<'a>) -> Self {
        Self { iw, exit }
    }

    pub fn build_lvalue(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Lvalue,
        locals: &Scope<'a>,
    ) -> Result<ResolvedLvalue<'a>, Error> {
        match node {
            Lvalue::Identifier(ident) => {
                if let Some(vi) = locals.find_variable(ident, true) {
                    return Ok(ResolvedLvalue {
                        ptr: vi.alloca,
                        rw: vi.rw,
                        var: Some(vi.clone()),
                    });
                }

                if let Some(gb) = self.iw.module.get_global(ident) {
                    return Ok(ResolvedLvalue {
                        ptr: gb.as_pointer_value(),
                        rw: false,
                        var: None,
                    });
                }

                if let Some(fv) = locals.find_function(ident, true) {
                    return Ok(ResolvedLvalue {
                        ptr: fv.as_global_value().as_pointer_value(),
                        rw: false,
                        var: None,
                    });
                }

                Err(Error::IdentifierNotFound(ident.clone()))
            }
            Lvalue::Increment(base_lv) => {
                let base = self.build_lvalue(builder, fd, base_lv.as_ref(), locals);
                if let Err(err) = &base {
                    return Err(err.clone());
                }
                let pv = base.unwrap();
                if !pv.rw {
                    let name = format!("{base_lv}");
                    return Err(Error::ReadOnlyIdentifier(name));
                }
                let ptr = pv.ptr;
                let pointee = ptr.get_type().get_element_type();
                if pointee.is_int_type() && !TypeBuilder::is_boolean_int(pointee.into_int_type()) {
                    let load = builder.build_load(ptr, "").into_int_value();
                    let add =
                        builder.build_int_add(load, self.iw.builtins.one(load.get_type()), "");
                    builder.build_store(ptr, add);
                    pv.mark_written();
                    Ok(pv)
                } else {
                    Err(Error::UnexpectedType(Some("integer".to_owned())))
                }
            }
            Lvalue::Decrement(base_lv) => {
                let base = self.build_lvalue(builder, fd, base_lv.as_ref(), locals);
                if let Err(err) = &base {
                    return Err(err.clone());
                }
                let pv = base.unwrap();
                if !pv.rw {
                    let name = format!("{base_lv}");
                    return Err(Error::ReadOnlyIdentifier(name));
                }
                let ptr = pv.ptr;
                let pointee = ptr.get_type().get_element_type();
                if pointee.is_int_type() && !TypeBuilder::is_boolean_int(pointee.into_int_type()) {
                    let load = builder.build_load(ptr, "").into_int_value();
                    let add =
                        builder.build_int_sub(load, self.iw.builtins.one(load.get_type()), "");
                    builder.build_store(ptr, add);
                    pv.mark_written();
                    Ok(pv)
                } else {
                    Err(Error::UnexpectedType(Some("integer".to_owned())))
                }
            }
            Lvalue::Dotted(base, field_name) => {
                let tb = TypeBuilder::new(self.iw.clone());

                let base = self.build_lvalue(builder, fd, base.as_ref(), locals);
                if let Err(err) = &base {
                    return Err(err.clone());
                }
                let pv = base.unwrap();

                let pointee_type = pv.ptr.get_type().get_element_type();

                if let Some(struct_type) = tb.is_refcounted_any_type(pointee_type) {
                    if let Some(struct_def) = tb.struct_by_name(struct_type) {
                        if let Some(idx) = struct_def.field_idx_by_name(field_name) {
                            let i32_0 = self.iw.builtins.zero(self.iw.builtins.int32);
                            let i32_idx = self.iw.builtins.n(idx as u64, self.iw.builtins.int32);
                            let load_pv = builder.build_load(pv.ptr, "").into_pointer_value();
                            let gep = unsafe {
                                builder.build_gep(load_pv, &[i32_0, i32_idx], field_name)
                            };
                            Ok(ResolvedLvalue {
                                ptr: gep,
                                rw: true,
                                var: None,
                            })
                        } else {
                            Err(Error::FieldNotFound(String::from(field_name)))
                        }
                    } else {
                        Err(Error::DotAccessInvalid)
                    }
                } else if let Some(struct_type) = tb.is_value_any_type(pointee_type) {
                    if let Some(struct_def) = tb.struct_by_name(struct_type) {
                        if let Some(idx) = struct_def.field_idx_by_name(field_name) {
                            let gep = builder
                                .build_struct_gep(pv.ptr, idx as u32, field_name)
                                .unwrap();
                            return Ok(ResolvedLvalue {
                                ptr: gep,
                                rw: true,
                                var: None,
                            });
                        } else {
                            return Err(Error::FieldNotFound(String::from(field_name)));
                        }
                    } else {
                        return Err(Error::DotAccessInvalid);
                    }
                } else {
                    return Err(Error::DotAccessInvalid);
                }
            }
            Lvalue::Indexed(base, idx) => {
                let tb = TypeBuilder::new(self.iw.clone());
                let eb = ExpressionBuilder::new(self.iw.clone(), self.exit);
                let eval_base = self.build_lvalue(builder, fd, base.as_ref(), locals);
                let eval_idx = eb.build_expr(builder, fd, idx.as_ref(), locals, None);

                match (eval_base, eval_idx) {
                    (Ok(_), None) => Err(Error::InvalidExpression),
                    (Err(err), _) => Err(err),
                    (Ok(base_obj), Some(idx_obj)) => {
                        let is_arr = base_obj.ptr.get_type().get_element_type().is_array_type();
                        let is_ptr = base_obj.ptr.get_type().get_element_type().is_pointer_type();
                        let is_tuple = base_obj.ptr.get_type().get_element_type().is_struct_type()
                            && TypeBuilder::is_tuple_type(
                                base_obj
                                    .ptr
                                    .get_type()
                                    .get_element_type()
                                    .into_struct_type(),
                            );
                        if !(is_arr || is_ptr || is_tuple) {
                            return Err(Error::UnexpectedType(Some("indexable base".to_owned())));
                        }
                        if !idx_obj.get_type().is_int_type() {
                            return Err(Error::UnexpectedType(Some("integer index".to_owned())));
                        }
                        let idx0 = self.iw.builtins.zero(self.iw.builtins.int32);
                        let ptr: PointerValue = unsafe {
                            if is_arr {
                                builder.build_in_bounds_gep(
                                    base_obj.ptr,
                                    &[idx0, idx_obj.into_int_value()],
                                    "",
                                )
                            } else if is_tuple {
                                builder.build_in_bounds_gep(
                                    base_obj.ptr,
                                    &[
                                        idx0,
                                        idx_obj
                                            .into_int_value()
                                            .const_cast(self.iw.builtins.int32, false),
                                    ],
                                    "",
                                )
                            } else {
                                let ptr_as_int = builder.build_ptr_to_int(
                                    builder.build_load(base_obj.ptr, "").into_pointer_value(),
                                    self.iw.builtins.int64,
                                    "",
                                );
                                let ptr_elem_type = BasicTypeEnum::try_from(
                                    base_obj
                                        .ptr
                                        .get_type()
                                        .get_element_type()
                                        .into_pointer_type()
                                        .get_element_type(),
                                )
                                .unwrap();
                                let ptr_elem_size = tb.sizeof(ptr_elem_type);
                                let total_offset = builder.build_int_mul(
                                    idx_obj.into_int_value(),
                                    ptr_elem_size,
                                    "",
                                );
                                builder.build_int_to_ptr(
                                    builder.build_int_add(ptr_as_int, total_offset, ""),
                                    base_obj
                                        .ptr
                                        .get_type()
                                        .get_element_type()
                                        .into_pointer_type(),
                                    "",
                                )
                            }
                        };
                        Ok(ResolvedLvalue {
                            ptr,
                            rw: true,
                            var: None,
                        })
                    }
                }
            }
        }
    }
}
