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

use std::cmp::max;

use inkwell::{
    builder::Builder,
    types::{BasicTypeEnum, FloatType, IntType, StructType},
    values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, IntValue, PointerValue},
    FloatPredicate, IntPredicate,
};

use crate::{
    ast::{AllocInitializer, Expr, Expression, FunctionDefinition},
    builders::{
        lvalue::LvalueBuilder,
        refcount::{
            alloc_refcounted_type, insert_getref_if_refcounted, insert_incref_if_refcounted,
        },
        ty::TypeBuilder,
    },
    codegen::{
        callable::{Call, Callable},
        structure::Method,
    },
    err::{CompilerError, Error},
    iw::CompilerCore,
};

use super::{func::FunctionExitData, scope::Scope};

pub struct ExpressionBuilder<'a, 'b> {
    pub iw: CompilerCore<'a>,
    pub tb: TypeBuilder<'a>,
    pub lvb: LvalueBuilder<'a, 'b>,
    pub exit: &'b FunctionExitData<'a>,
}

#[derive(Clone)]
pub enum FunctionCallArgument<'a> {
    Expr(Expression),
    Value(BasicMetadataValueEnum<'a>),
}

impl<'a, 'b> ExpressionBuilder<'a, 'b> {
    pub fn new(iw: CompilerCore<'a>, exit: &'b FunctionExitData<'a>) -> Self {
        Self {
            iw: iw.clone(),
            tb: TypeBuilder::new(iw.clone()),
            lvb: LvalueBuilder::new(iw.clone(), exit),
            exit,
        }
    }

    fn widen_flt_if_needed(
        &self,
        builder: &Builder<'a>,
        x: FloatValue<'a>,
        y: FloatValue<'a>,
    ) -> (FloatValue<'a>, FloatValue<'a>) {
        let x_type = x.get_type();
        let y_type = y.get_type();
        if x_type == y_type {
            // both 32 or both 64
            (x, y)
        } else if x_type == self.iw.builtins.float64 {
            // then y must be float32
            assert!(y_type == self.iw.builtins.float32);
            let y = builder.build_float_ext(y, x_type, "");
            (x, y)
        } else {
            // then x must be float32
            assert!(x_type == self.iw.builtins.float32);
            let x = builder.build_float_ext(x, y_type, "");
            (x, y)
        }
    }

    fn widen_int_if_needed(
        &self,
        builder: &Builder<'a>,
        x: IntValue<'a>,
        y: IntValue<'a>,
        op: &Expr,
    ) -> (IntValue<'a>, IntValue<'a>) {
        let x_wide = x.get_type().get_bit_width();
        let y_wide = y.get_type().get_bit_width();
        if x_wide == y_wide {
            return (x, y);
        }
        let unsigned = (x_wide == 1 || y_wide == 1) || op.is_unsigned_operation();
        let max_wide = max(x_wide, y_wide);
        let max_wide_type = self.iw.context.custom_width_int_type(max_wide);
        let x = if unsigned {
            builder.build_int_z_extend(x, max_wide_type, "")
        } else {
            builder.build_int_s_extend(x, max_wide_type, "")
        };
        let y = if unsigned {
            builder.build_int_z_extend(y, max_wide_type, "")
        } else {
            builder.build_int_s_extend(y, max_wide_type, "")
        };
        (x, y)
    }

    fn build_int_bin_op(
        &self,
        builder: &Builder<'a>,
        x: IntValue<'a>,
        y: IntValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        let (x, y) = self.widen_int_if_needed(builder, x, y, op);
        Some(BasicValueEnum::IntValue(match op {
            Expr::Addition(..) => builder.build_int_add(x, y, ""),
            Expr::Subtraction(..) => builder.build_int_sub(x, y, ""),
            Expr::Multiplication(..) => builder.build_int_mul(x, y, ""),
            Expr::SignedDivision(..) => builder.build_int_signed_div(x, y, ""),
            Expr::SignedModulo(..) => builder.build_int_signed_rem(x, y, ""),
            Expr::UnsignedDivision(..) => builder.build_int_unsigned_div(x, y, ""),
            Expr::UnsignedModulo(..) => builder.build_int_unsigned_rem(x, y, ""),
            Expr::Equality(..) => builder.build_int_compare(IntPredicate::EQ, x, y, ""),
            Expr::NotEqual(..) => builder.build_int_compare(IntPredicate::NE, x, y, ""),
            Expr::SignedGreaterThan(..) => builder.build_int_compare(IntPredicate::SGT, x, y, ""),
            Expr::SignedLessThan(..) => builder.build_int_compare(IntPredicate::SLT, x, y, ""),
            Expr::SignedGreaterEqual(..) => builder.build_int_compare(IntPredicate::SGE, x, y, ""),
            Expr::SignedLessEqual(..) => builder.build_int_compare(IntPredicate::SLE, x, y, ""),
            Expr::UnsignedGreaterThan(..) => builder.build_int_compare(IntPredicate::UGT, x, y, ""),
            Expr::UnsignedLessThan(..) => builder.build_int_compare(IntPredicate::ULT, x, y, ""),
            Expr::UnsignedGreaterEqual(..) => {
                builder.build_int_compare(IntPredicate::UGE, x, y, "")
            }
            Expr::UnsignedLessEqual(..) => builder.build_int_compare(IntPredicate::ULE, x, y, ""),
            Expr::And(..) => builder.build_and(x, y, ""),
            Expr::Or(..) => builder.build_or(x, y, ""),
            Expr::XOr(..) => builder.build_xor(x, y, ""),
            Expr::ShiftLeft(..) => builder.build_left_shift(x, y, ""),
            Expr::ShiftRight(..) => builder.build_right_shift(x, y, true, ""),
            _ => panic!(""),
        }))
    }

    fn build_ptr_bin_op(
        &self,
        builder: &Builder<'a>,
        x: PointerValue<'a>,
        y: PointerValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        Some(BasicValueEnum::IntValue(match op {
            Expr::Identity(..) => {
                let diff = builder.build_ptr_diff(x, y, "");
                let zero = diff.get_type().const_zero();
                builder.build_int_compare(IntPredicate::EQ, diff, zero, "")
            }
            _ => panic!(""),
        }))
    }

    fn build_flt_bin_op(
        &self,
        builder: &Builder<'a>,
        x: FloatValue<'a>,
        y: FloatValue<'a>,
        node: &Expression,
    ) -> Option<BasicValueEnum<'a>> {
        use BasicValueEnum::{FloatValue, IntValue};
        let (x, y) = self.widen_flt_if_needed(builder, x, y);
        Some(match node.payload {
            Expr::Addition(..) => FloatValue(builder.build_float_add(x, y, "")),
            Expr::Subtraction(..) => FloatValue(builder.build_float_sub(x, y, "")),
            Expr::Multiplication(..) => FloatValue(builder.build_float_mul(x, y, "")),
            Expr::SignedDivision(..) => FloatValue(builder.build_float_div(x, y, "")),
            Expr::SignedModulo(..) => FloatValue(builder.build_float_rem(x, y, "")),
            Expr::Equality(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OEQ, x, y, ""))
            }
            Expr::NotEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::ONE, x, y, ""))
            }
            Expr::SignedGreaterThan(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OGT, x, y, ""))
            }
            Expr::SignedLessThan(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OLT, x, y, ""))
            }
            Expr::SignedGreaterEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OGE, x, y, ""))
            }
            Expr::SignedLessEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OLE, x, y, ""))
            }
            Expr::UnsignedDivision(..)
            | Expr::UnsignedModulo(..)
            | Expr::UnsignedGreaterEqual(..)
            | Expr::UnsignedGreaterThan(..)
            | Expr::UnsignedLessEqual(..)
            | Expr::UnsignedLessThan(..) => {
                self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                    node.loc,
                    Error::UnsignedFloatUnsupported,
                ));
                return None;
            }
            _ => panic!(""),
        })
    }

    pub fn build_expr(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        locals: &Scope<'a>,
        type_hint: Option<BasicTypeEnum<'a>>,
    ) -> Option<BasicValueEnum<'a>> {
        self.do_build_expr(builder, fd, node, locals, type_hint)
    }

    fn resolve_const_int(&self, n: i64, th: Option<IntType<'a>>) -> IntValue<'a> {
        let ty = th.unwrap_or(self.iw.builtins.default_int_type);
        self.iw.builtins.n(n as u64, ty)
    }

    fn resolve_const_float(&self, n: f64, th: Option<FloatType<'a>>) -> FloatValue<'a> {
        let ty = th.unwrap_or(self.iw.builtins.default_float_type);
        self.iw.builtins.flt_n(n, ty)
    }

    #[allow(clippy::too_many_arguments)]
    fn alloc_by_initializer(
        &self,
        builder: &Builder<'a>,
        locals: &Scope<'a>,
        struct_def: &crate::codegen::structure::Structure<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        self_arg: FunctionCallArgument<'a>,
        args: &[Expression],
    ) -> bool {
        let mut eval_args: Vec<FunctionCallArgument> = vec![self_arg];

        args.iter()
            .for_each(|arg| eval_args.push(FunctionCallArgument::Expr(arg.clone())));
        let init_r = Callable::from_overload_set(
            self,
            builder,
            fd,
            locals,
            "init",
            &eval_args,
            struct_def.init.borrow().as_ref(),
        );
        if let Ok(init_func) = init_r {
            if let Some(call_obj) =
                Call::try_build(self, builder, fd, locals, &eval_args, init_func)
            {
                call_obj.build_call(self, builder, node);
                true
            } else {
                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::InvalidExpression));
                false
            }
        } else {
            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                node.loc,
                Error::FieldNotFound(String::from("init")),
            ));
            false
        }
    }

    fn check_allowed_allocation(
        &self,
        ty: StructType<'a>,
        node: &Expression,
        init: &Option<AllocInitializer>,
    ) -> Option<crate::codegen::structure::Structure<'a>> {
        let struct_def = self.tb.structure_by_llvm_type(ty);
        let struct_def = struct_def?;

        match init {
            Some(ai) => match ai {
                AllocInitializer::ByFieldList(..) => {
                    return if struct_def.has_explicit_init() {
                        self.iw
                            .diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(node.loc, Error::InitMustBeUsed));
                        None
                    } else {
                        Some(struct_def)
                    };
                }
                AllocInitializer::ByInit(..) => Some(struct_def),
            },
            None => {
                return if struct_def.has_explicit_init() {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, Error::InitMustBeUsed));
                    None
                } else {
                    Some(struct_def)
                };
            }
        }
    }

    fn alloc_value_type(
        &self,
        builder: &Builder<'a>,
        locals: &Scope<'a>,
        ty: StructType<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        init: &Option<AllocInitializer>,
    ) -> Option<BasicValueEnum<'a>> {
        let struct_def = self.check_allowed_allocation(ty, node, init)?;
        let val_alloca = self.exit.create_alloca(
            builder,
            ty,
            Some("temp_alloc"),
            Some(super::func::AllocaInitialValue::Zero),
        );

        match init {
            Some(ai) => match ai {
                AllocInitializer::ByFieldList(init_list) => {
                    let mut val = builder.build_load(val_alloca, "").into_struct_value();
                    for fi in init_list {
                        if let Some(idx) = struct_def.field_idx_by_name(&fi.field) {
                            let type_hint = struct_def.field_type_by_name(&fi.field);
                            if let Some(finit) =
                                self.build_expr(builder, fd, fi.value.as_ref(), locals, type_hint)
                            {
                                val = builder
                                    .build_insert_value(val, finit, idx as u32, "")
                                    .unwrap()
                                    .into_struct_value();
                            } else {
                                self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                    fi.value.loc,
                                    Error::InvalidExpression,
                                ));
                                return None;
                            }
                        } else {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                node.loc,
                                Error::FieldNotFound(fi.field.clone()),
                            ));
                            return None;
                        }
                    }
                    builder.build_store(val_alloca, val);
                }
                AllocInitializer::ByInit(args) => {
                    let self_arg = FunctionCallArgument::Value(val_alloca.into());
                    self.alloc_by_initializer(
                        builder,
                        locals,
                        &struct_def,
                        fd,
                        node,
                        self_arg,
                        args,
                    );
                }
            },
            None => {}
        }

        Some(builder.build_load(val_alloca, ""))
    }

    fn alloc_ref_type(
        &self,
        builder: &Builder<'a>,
        locals: &Scope<'a>,
        ty: StructType<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        init: &Option<AllocInitializer>,
    ) -> Option<BasicValueEnum<'a>> {
        let struct_def = self.check_allowed_allocation(ty, node, init)?;

        let pv = alloc_refcounted_type(&self.iw, builder, ty);
        let temp_pv = self.exit.create_alloca(
            builder,
            pv.get_type(),
            Some("temp_alloc"),
            Some(super::func::AllocaInitialValue::Zero),
        );
        builder.build_store(temp_pv, pv);
        let ret = builder.build_load(temp_pv, "");
        self.exit.decref_on_exit(temp_pv);

        match init {
            Some(ai) => match ai {
                AllocInitializer::ByFieldList(init_list) => {
                    for fi in init_list {
                        if let Some(idx) = struct_def.field_idx_by_name(&fi.field) {
                            let type_hint = struct_def.field_type_by_name(&fi.field);
                            if let Some(finit) =
                                self.build_expr(builder, fd, fi.value.as_ref(), locals, type_hint)
                            {
                                let zero = self.iw.builtins.zero(self.iw.builtins.int32);
                                let idx = self.iw.builtins.n(idx as u64, self.iw.builtins.int32);
                                let gep = unsafe { builder.build_gep(pv, &[zero, idx], "") };
                                builder.build_store(gep, finit);
                            } else {
                                self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                    fi.value.loc,
                                    Error::InvalidExpression,
                                ));
                                return None;
                            }
                        } else {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                node.loc,
                                Error::FieldNotFound(fi.field.clone()),
                            ));
                            return None;
                        }
                    }
                }
                AllocInitializer::ByInit(args) => {
                    let self_arg =
                        FunctionCallArgument::Value(BasicMetadataValueEnum::PointerValue(pv));
                    self.alloc_by_initializer(
                        builder,
                        locals,
                        &struct_def,
                        fd,
                        node,
                        self_arg,
                        args,
                    );
                }
            },
            None => {}
        }

        Some(ret)
    }

    fn get_binop_args(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        x: &Expression,
        y: &Expression,
        locals: &Scope<'a>,
        type_hint: Option<BasicTypeEnum<'a>>,
    ) -> (Option<BasicValueEnum<'a>>, Option<BasicValueEnum<'a>>) {
        let mut th = type_hint;
        let bx = self.build_expr(builder, fd, x, locals, th);
        if th.is_none() {
            th = bx.map(|bv| bv.get_type());
        }
        let by = self.build_expr(builder, fd, y, locals, th);
        (bx, by)
    }

    fn do_build_expr(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        locals: &Scope<'a>,
        type_hint: Option<BasicTypeEnum<'a>>,
    ) -> Option<BasicValueEnum<'a>> {
        use crate::ast::Expr::*;
        use BasicValueEnum::{FloatValue, IntValue, PointerValue};

        match &node.payload {
            ConstantNumber(cnum) => {
                use crate::ast::Number::*;
                return match cnum {
                    Integer(n) => {
                        let th: Option<IntType> = if let Some(type_hint) = type_hint {
                            match type_hint {
                                BasicTypeEnum::IntType(it) => Some(it),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        Some(IntValue(self.resolve_const_int(*n, th)))
                    }
                    FloatingPoint(f) => {
                        let th: Option<FloatType> = if let Some(type_hint) = type_hint {
                            match type_hint {
                                BasicTypeEnum::FloatType(ft) => Some(ft),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        Some(FloatValue(self.resolve_const_float(*f, th)))
                    }
                };
            }
            ConstString(s) => {
                let gv = builder.build_global_string_ptr(s, "");
                gv.set_linkage(inkwell::module::Linkage::Internal);
                Some(PointerValue(gv.as_pointer_value()))
            }
            Addition(x, y) | Subtraction(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, node);
                }

                if let (Some(PointerValue(px)), Some(IntValue(iy))) = (bx, by) {
                    let ix = builder.build_ptr_to_int(px, self.iw.builtins.int64, "");
                    let st = px.get_type().get_element_type().size_of().unwrap();
                    let iy_sized = builder.build_int_mul(iy, st, "");
                    let ix_inc = self
                        .build_int_bin_op(builder, ix, iy_sized, &node.payload)
                        .unwrap()
                        .into_int_value();
                    let px_inc = builder.build_int_to_ptr(ix_inc, px.get_type(), "");
                    return Some(PointerValue(px_inc));
                }

                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            Multiplication(x, y)
            | SignedDivision(x, y)
            | SignedModulo(x, y)
            | UnsignedDivision(x, y)
            | UnsignedModulo(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, node);
                }

                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            And(x, y) | Or(x, y) | XOr(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                return if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    self.build_int_bin_op(builder, ix, iy, &node.payload)
                } else {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                };
            }
            ShiftLeft(x, y) | ShiftRight(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                return if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    self.build_int_bin_op(builder, ix, iy, &node.payload)
                } else {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                };
            }
            UnaryMinus(x) => {
                let bx = self.build_expr(builder, fd, x.as_ref(), locals, type_hint);
                if let Some(IntValue(x)) = bx {
                    Some(IntValue(builder.build_int_neg(x, "")))
                } else if let Some(FloatValue(x)) = bx {
                    Some(FloatValue(builder.build_float_neg(x, "")))
                } else {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                }
            }
            UnaryNot(x) => {
                let bx = self.build_expr(builder, fd, x.as_ref(), locals, type_hint);
                if let Some(IntValue(x)) = bx {
                    Some(IntValue(builder.build_not(x, "")))
                } else {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                }
            }
            SignedGreaterThan(x, y)
            | SignedGreaterEqual(x, y)
            | SignedLessThan(x, y)
            | SignedLessEqual(x, y)
            | UnsignedGreaterEqual(x, y)
            | UnsignedLessThan(x, y)
            | UnsignedGreaterThan(x, y)
            | UnsignedLessEqual(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, node);
                }

                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            Equality(x, y) | NotEqual(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, node);
                }

                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            Identity(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(PointerValue(ix)), Some(PointerValue(iy))) = (bx, by) {
                    return self.build_ptr_bin_op(builder, ix, iy, &node.payload);
                }

                self.iw
                    .diagnostics
                    .borrow_mut()
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            FunctionCall(id, args) => {
                let mut fv: Option<Callable<'a>> = None;
                if let Some(fbyname) = locals.find_function(id, true) {
                    fv = Some(Callable::from_function(fbyname));
                } else {
                    let candidate_expr = Expression {
                        loc: node.loc,
                        payload: Expr::Rvalue(crate::ast::Lvalue::Identifier(id.clone())),
                    };
                    if let Some(PointerValue(value)) =
                        self.build_expr(builder, fd, &candidate_expr, locals, type_hint)
                    {
                        if value.get_type().get_element_type().is_function_type() {
                            fv = Callable::from_pointer(value);
                        }
                    }
                }

                if fv.is_none() {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::IdentifierNotFound(id.clone()),
                    ));
                    return None;
                }
                let fv = fv.unwrap();

                let f_args: Vec<FunctionCallArgument> = args
                    .iter()
                    .map(|arg| FunctionCallArgument::Expr(arg.clone()))
                    .collect();
                return if let Some(call_obj) =
                    Call::try_build(self, builder, fd, locals, &f_args, fv)
                {
                    call_obj.build_call(self, builder, node)
                } else {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::UnexpectedType(Some("callable function".to_owned())),
                    ));
                    None
                };
            }
            MethodCall(mc) => {
                let this_lvalue = self.lvb.build_lvalue(builder, fd, &mc.this, locals);
                if this_lvalue.is_err() {
                    return None;
                }
                let this_lvalue = this_lvalue.unwrap();
                let this = builder.build_load(this_lvalue.ptr, "");

                let mut method_decls: Vec<Method<'a>> = vec![];
                let mut this_arg: Option<BasicMetadataValueEnum<'a>> = None;
                let mut matched = false;

                if let Some(this_type) = self.tb.is_refcounted_basic_type(this.get_type()) {
                    if let Some(let_this_decl) = self.tb.structure_by_llvm_type(this_type) {
                        method_decls = let_this_decl.method_by_name(&mc.name);
                        if method_decls.is_empty() {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                node.loc,
                                Error::IdentifierNotFound(mc.name.clone()),
                            ));
                            return None;
                        }
                        this_arg = Some(BasicMetadataValueEnum::PointerValue(
                            this.into_pointer_value(),
                        ));
                        matched = true;
                    }
                } else if let Some(this_type) = self.tb.is_value_basic_type(this.get_type()) {
                    if let Some(let_this_decl) = self.tb.structure_by_llvm_type(this_type) {
                        method_decls = let_this_decl.method_by_name(&mc.name);
                        if method_decls.is_empty() {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                node.loc,
                                Error::IdentifierNotFound(mc.name.clone()),
                            ));
                            return None;
                        }
                        this_arg = Some(BasicMetadataValueEnum::PointerValue(
                            if this.is_pointer_value() {
                                this.into_pointer_value()
                            } else {
                                this_lvalue.ptr
                            },
                        ));
                        matched = true;
                    }
                } else {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::UnexpectedType(Some("value or refcounted type".to_owned())),
                    ));
                    return None;
                }

                if !matched {
                    return None;
                }

                let method_funcs: Vec<_> = method_decls.iter().map(|md| md.func).collect();
                let mut f_args: Vec<FunctionCallArgument> = mc
                    .args
                    .iter()
                    .map(|arg| FunctionCallArgument::Expr(arg.clone()))
                    .collect();
                f_args.insert(0, FunctionCallArgument::Value(this_arg.unwrap()));

                let resolved_callable = Callable::from_overload_set(
                    self,
                    builder,
                    fd,
                    locals,
                    &mc.name,
                    &f_args,
                    &method_funcs,
                );
                if let Err(err) = resolved_callable {
                    self.iw
                        .diagnostics
                        .borrow_mut()
                        .error(CompilerError::new(node.loc, err));
                    return None;
                }
                let method_func = resolved_callable.unwrap();

                return if let Some(call_obj) =
                    Call::try_build(self, builder, fd, locals, &f_args, method_func)
                {
                    call_obj.build_call(self, builder, node)
                } else {
                    None
                };
            }
            Alloc(ty, init) => {
                if let Some(basic_type) = self.tb.llvm_type_by_descriptor(locals, ty) {
                    if let Some(struct_type) = self.tb.is_refcounted_basic_type(basic_type) {
                        return self.alloc_ref_type(builder, locals, struct_type, fd, node, init);
                    } else if let Some(struct_type) = self.tb.is_value_basic_type(basic_type) {
                        return self.alloc_value_type(builder, locals, struct_type, fd, node, init);
                    } else {
                        self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(Some(ty.clone())),
                        ));
                        return None;
                    }
                } else {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::TypeNotFound(ty.clone()),
                    ));
                    None
                }
            }
            Incref(e) => {
                if let Some(expr) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if self.tb.is_refcounted_basic_type(expr.get_type()).is_some() {
                        insert_incref_if_refcounted(&self.iw, builder, expr);
                        Some(expr)
                    } else {
                        self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(
                                self.tb.descriptor_by_llvm_type(expr.get_type()),
                            ),
                        ));
                        None
                    }
                } else {
                    None
                }
            }
            Getref(e) => {
                if let Some(expr) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if self.tb.is_refcounted_basic_type(expr.get_type()).is_some() {
                        if let Some(val) = insert_getref_if_refcounted(&self.iw, builder, expr) {
                            return Some(BasicValueEnum::IntValue(val));
                        } else {
                            self.iw
                                .diagnostics
                                .borrow_mut()
                                .error(CompilerError::new(node.loc, Error::InvalidExpression));
                            None
                        }
                    } else {
                        self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(
                                self.tb.descriptor_by_llvm_type(expr.get_type()),
                            ),
                        ));
                        None
                    }
                } else {
                    None
                }
            }
            Rvalue(lv) => {
                let rlv = self.lvb.build_lvalue(builder, fd, lv, locals);
                return match rlv {
                    Ok(pv) => {
                        // there is no usable way to "load" a function, so if we detect that
                        // the lvalue is a ptr-to-func, just return it directly because
                        // most likely that's what was meant
                        let name = format!("load_{}", String::from(lv));
                        if pv.ptr.get_type().get_element_type().is_function_type() {
                            Some(PointerValue(pv.ptr))
                        } else {
                            Some(builder.build_load(pv.ptr, &name))
                        }
                    }
                    Err(err) => {
                        self.iw
                            .diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(node.loc, err));
                        None
                    }
                };
            }
            Cast(e, t, unsigned) => {
                if let Some(expr) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if let Some(ty) = self.tb.llvm_type_by_descriptor(locals, t) {
                        if let Some(ret) =
                            self.tb.build_cast(builder, expr, ty, node.loc, *unsigned)
                        {
                            Some(ret)
                        } else {
                            self.iw
                                .diagnostics
                                .borrow_mut()
                                .error(CompilerError::new(node.loc, Error::InvalidCast));
                            None
                        }
                    } else {
                        self.iw
                            .diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(e.loc, Error::TypeNotFound(t.clone())));
                        None
                    }
                } else {
                    None
                }
            }
            Array(exprs) => {
                let mut eval_exprs: Vec<BasicValueEnum> = vec![];
                for expr in exprs {
                    if let Some(eval) = self.build_expr(builder, fd, expr, locals, type_hint) {
                        if self.tb.is_refcounted_basic_type(eval.get_type()).is_some() {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                expr.loc,
                                Error::RefTypeInValTypeForbidden,
                            ));
                            return None;
                        } else if eval_exprs.is_empty() {
                            eval_exprs.push(eval);
                        } else if eval.get_type() != eval_exprs[0].get_type() {
                            self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                expr.loc,
                                Error::UnexpectedType(Some("uniform typed entries".to_owned())),
                            ));
                            return None;
                        } else {
                            eval_exprs.push(eval);
                        }
                    } else {
                        return None;
                    }
                }

                let elem_ty = eval_exprs[0].get_type();
                let len = eval_exprs.len();
                let arr_ty = self.tb.llvm_array_type(elem_ty, len as u32);
                let arr_ptr = self.exit.create_alloca(builder, arr_ty, None, None);
                let mut arr = builder.build_load(arr_ptr, "").into_array_value();
                for (i, eval_expr) in eval_exprs.iter().enumerate().take(len) {
                    arr = builder
                        .build_insert_value(arr, *eval_expr, i as u32, "")
                        .unwrap()
                        .into_array_value();
                }

                return Some(BasicValueEnum::ArrayValue(arr));
            }
            Tuple(exprs) => {
                // this seems tidier than a match + if combination, but clippy disagrees
                #[allow(clippy::unnecessary_unwrap)]
                let type_hints: Vec<BasicTypeEnum> = if type_hint.is_some()
                    && type_hint.unwrap().is_struct_type()
                    && type_hint
                        .unwrap()
                        .into_struct_type()
                        .get_field_types()
                        .len()
                        == exprs.len()
                {
                    // jackpot - we can use the type_hint to construct each element of the tuple!
                    type_hint.unwrap().into_struct_type().get_field_types()
                } else {
                    vec![]
                };
                let mut eval_exprs: Vec<BasicValueEnum> = vec![];
                let mut eval_types: Vec<BasicTypeEnum> = vec![];
                for expr in exprs.iter().enumerate() {
                    let type_hint = type_hints.get(expr.0).copied();
                    if let Some(eval) = self.build_expr(builder, fd, expr.1, locals, type_hint) {
                        eval_exprs.push(eval);
                        eval_types.push(eval.get_type());
                    } else {
                        return None;
                    }
                }

                let tuple_struct_type = self.iw.context.struct_type(&eval_types, false);
                let tuple_struct_alloca = self.exit.create_alloca(
                    builder,
                    tuple_struct_type,
                    None,
                    Some(crate::builders::func::AllocaInitialValue::Zero),
                );
                let mut tuple_struct_value = builder
                    .build_load(tuple_struct_alloca, "")
                    .into_struct_value();
                for (idx, val) in eval_exprs.iter().enumerate() {
                    tuple_struct_value = builder
                        .build_insert_value(tuple_struct_value, *val, idx as u32, "")
                        .unwrap()
                        .into_struct_value();
                }

                if self.tb.is_valtype_with_refcount_field(tuple_struct_type) {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::RefTypeInValTypeForbidden,
                    ));
                    return None;
                }

                return Some(BasicValueEnum::StructValue(tuple_struct_value));
            }
            PropertyofVar(e, tp) => self
                .build_expr(builder, fd, e.as_ref(), locals, type_hint)
                .map(|expr| {
                    BasicValueEnum::IntValue(match tp {
                        crate::ast::TypeProperty::Size => self.tb.sizeof(expr.get_type()),
                        crate::ast::TypeProperty::Alignment => self.tb.alignof(expr.get_type()),
                    })
                }),
            PropertyofType(ident, tp) => {
                return if let Some(ty) = self.tb.llvm_type_by_descriptor(locals, ident) {
                    if let Some(struct_type) = self.tb.is_refcounted_basic_type(ty) {
                        Some(BasicValueEnum::IntValue(match tp {
                            crate::ast::TypeProperty::Size => {
                                self.tb.sizeof(BasicTypeEnum::StructType(struct_type))
                            }
                            crate::ast::TypeProperty::Alignment => {
                                self.tb.alignof(BasicTypeEnum::StructType(struct_type))
                            }
                        }))
                    } else {
                        Some(BasicValueEnum::IntValue(match tp {
                            crate::ast::TypeProperty::Size => self.tb.sizeof(ty),
                            crate::ast::TypeProperty::Alignment => self.tb.alignof(ty),
                        }))
                    }
                } else {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        node.loc,
                        Error::TypeNotFound(ident.clone()),
                    ));
                    None
                }
            }
            AddressOf(lv) => {
                let lv = self.lvb.build_lvalue(builder, fd, lv, locals);
                return match lv {
                    Ok(pv) => Some(PointerValue(pv.ptr)),
                    Err(err) => {
                        self.iw
                            .diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(node.loc, err));
                        None
                    }
                };
            }
            Deref(e) => {
                if let Some(ev) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if self.tb.is_refcounted_basic_type(ev.get_type()).is_some() {
                        self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                            e.loc,
                            Error::UnexpectedType(Some("not a refcounted type".to_owned())),
                        ));
                        None
                    } else if let PointerValue(pv) = ev {
                        return Some(builder.build_load(pv, ""));
                    } else {
                        self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                            e.loc,
                            Error::UnexpectedType(Some("pointer type".to_owned())),
                        ));
                        return None;
                    }
                } else {
                    self.iw.diagnostics.borrow_mut().error(CompilerError::new(
                        e.loc,
                        Error::UnexpectedType(Some("valid pointer expression".to_owned())),
                    ));
                    None
                }
            }
        }
    }
}
