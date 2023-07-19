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

use either::Either;
use inkwell::{
    builder::Builder,
    types::{BasicTypeEnum, FloatType, FunctionType, IntType, StructType},
    values::{
        BasicMetadataValueEnum, BasicValueEnum, CallableValue, FloatValue, FunctionValue, IntValue,
        PointerValue,
    },
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
    codegen::structure::Method,
    err::{CompilerError, Error},
    iw::CompilerCore,
};

use super::{func::FunctionExitData, scope::Scope};

pub struct ExpressionBuilder<'a, 'b> {
    iw: CompilerCore<'a>,
    tb: TypeBuilder<'a>,
    lvb: LvalueBuilder<'a, 'b>,
    exit: &'b FunctionExitData<'a>,
}

enum FunctionCallArgument<'a> {
    Expr(Expression),
    Value(BasicMetadataValueEnum<'a>),
}

struct FunctionCallData<'a> {
    dest: CallableValue<'a>,
    dest_src: Either<FunctionValue<'a>, PointerValue<'a>>,
    argc: usize,
    vararg: bool,
}

impl<'a> Clone for FunctionCallData<'a> {
    fn clone(&self) -> Self {
        let dest_clone: CallableValue<'a> = match self.dest_src {
            Either::Left(f) => CallableValue::from(f),
            Either::Right(p) => CallableValue::try_from(p).unwrap(),
        };

        Self {
            dest: dest_clone,
            dest_src: self.dest_src,
            argc: self.argc,
            vararg: self.vararg,
        }
    }
}

impl<'a> FunctionCallData<'a> {
    fn from_function(f: FunctionValue<'a>) -> Self {
        Self {
            dest: CallableValue::from(f),
            dest_src: Either::Left(f),
            argc: f.count_params() as usize,
            vararg: f.get_type().is_var_arg(),
        }
    }

    fn their_type(&self) -> FunctionType<'a> {
        match self.dest_src {
            Either::Left(fv) => fv.get_type(),
            Either::Right(fp) => fp.get_type().get_element_type().into_function_type(),
        }
    }

    fn from_pointer(p: PointerValue<'a>) -> Option<Self> {
        if let Ok(dest) = CallableValue::try_from(p) {
            let argc = p
                .get_type()
                .get_element_type()
                .into_function_type()
                .count_param_types() as usize;
            let vararg = p
                .get_type()
                .get_element_type()
                .into_function_type()
                .is_var_arg();
            Some(Self {
                dest,
                dest_src: Either::Right(p),
                argc,
                vararg,
            })
        } else {
            None
        }
    }

    fn check_arg_size_match(&self, args: &[BasicMetadataValueEnum]) -> bool {
        args.len() == self.argc || self.vararg
    }
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

    fn build_function_call(
        &self,
        node: &Expression,
        builder: &Builder<'a>,
        info: &FunctionCallData<'a>,
        args: &[BasicMetadataValueEnum<'a>],
    ) -> Option<BasicValueEnum<'a>> {
        if !info.check_arg_size_match(args) {
            self.iw.error(CompilerError::new(
                node.loc,
                Error::ArgCountMismatch(info.argc, args.len()),
            ));
            return None;
        }

        if let Some(obj) = builder
            .build_call(info.clone().dest, args, "")
            .try_as_basic_value()
            .left()
        {
            let temp_pv = builder.build_alloca(obj.get_type(), "temp_func");
            builder.build_store(temp_pv, obj);
            self.exit.decref_on_exit(temp_pv);
            Some(obj)
        } else {
            None
        }
    }

    fn build_function_call_args(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        locals: &Scope<'a>,
        args: &[FunctionCallArgument<'a>],
        their_type: FunctionType<'a>,
    ) -> Option<Vec<BasicMetadataValueEnum<'a>>> {
        let mut aargs: Vec<BasicMetadataValueEnum<'a>> = vec![];
        for (idx, arg) in args.iter().enumerate() {
            let type_hint = if their_type.get_param_types().len() > idx {
                Some(their_type.get_param_types()[idx])
            } else {
                None
            };
            match arg {
                FunctionCallArgument::Expr(expr) => {
                    if let Some(aarg) = self.build_expr(builder, fd, expr, locals, type_hint) {
                        let aarg_type = aarg.get_type();
                        let compat = type_hint.map_or(true, |ft| ft == aarg_type);
                        if compat {
                            aargs.push(BasicMetadataValueEnum::from(aarg));
                        } else {
                            // safe because compat is always true when no type hint is available
                            let exp_type = TypeBuilder::descriptor_by_llvm_type(type_hint.unwrap());
                            self.iw.error(CompilerError::new(
                                expr.loc,
                                Error::UnexpectedType(exp_type.map(|t| format!("{t}"))),
                            ));
                            return None;
                        }
                    } else {
                        self.iw
                            .error(CompilerError::new(expr.loc, Error::InvalidExpression));
                        return None;
                    }
                }
                FunctionCallArgument::Value(val) => aargs.push(*val),
            }
        }

        Some(aargs)
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
    ) -> (IntValue<'a>, IntValue<'a>) {
        let x_wide = x.get_type().get_bit_width();
        let y_wide = y.get_type().get_bit_width();
        if x_wide == y_wide {
            return (x, y);
        }
        // should boolean values be widened to int? eh..
        if x_wide == 1 || y_wide == 1 {
            return (x, y);
        }
        let max_wide = max(x_wide, y_wide);
        let max_wide_type = self.iw.context.custom_width_int_type(max_wide);
        let x = builder.build_int_s_extend(x, max_wide_type, "");
        let y = builder.build_int_s_extend(y, max_wide_type, "");
        (x, y)
    }

    fn build_int_bin_op(
        &self,
        builder: &Builder<'a>,
        x: IntValue<'a>,
        y: IntValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        let (x, y) = self.widen_int_if_needed(builder, x, y);
        Some(BasicValueEnum::IntValue(match op {
            Expr::Addition(..) => builder.build_int_add(x, y, ""),
            Expr::Subtraction(..) => builder.build_int_sub(x, y, ""),
            Expr::Multiplication(..) => builder.build_int_mul(x, y, ""),
            Expr::Division(..) => builder.build_int_signed_div(x, y, ""),
            Expr::Modulo(..) => builder.build_int_signed_rem(x, y, ""),
            Expr::Equality(..) => builder.build_int_compare(IntPredicate::EQ, x, y, ""),
            Expr::NotEqual(..) => builder.build_int_compare(IntPredicate::NE, x, y, ""),
            Expr::GreaterThan(..) => builder.build_int_compare(IntPredicate::SGT, x, y, ""),
            Expr::LessThan(..) => builder.build_int_compare(IntPredicate::SLT, x, y, ""),
            Expr::GreaterEqual(..) => builder.build_int_compare(IntPredicate::SGE, x, y, ""),
            Expr::LessEqual(..) => builder.build_int_compare(IntPredicate::SLE, x, y, ""),
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
        let ptr_diff = builder.build_ptr_diff(x, y, "");
        let zero = self.iw.builtins.zero(ptr_diff.get_type());
        self.build_int_bin_op(builder, ptr_diff, zero, op)
    }

    fn build_ptr_int_bin_op(
        &self,
        builder: &Builder<'a>,
        x: PointerValue<'a>,
        y: IntValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        let x_int = builder.build_ptr_to_int(x, y.get_type(), "");
        self.build_int_bin_op(builder, x_int, y, op)
    }

    fn build_flt_bin_op(
        &self,
        builder: &Builder<'a>,
        x: FloatValue<'a>,
        y: FloatValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        use BasicValueEnum::{FloatValue, IntValue};
        let (x, y) = self.widen_flt_if_needed(builder, x, y);
        Some(match op {
            Expr::Addition(..) => FloatValue(builder.build_float_add(x, y, "")),
            Expr::Subtraction(..) => FloatValue(builder.build_float_sub(x, y, "")),
            Expr::Multiplication(..) => FloatValue(builder.build_float_mul(x, y, "")),
            Expr::Division(..) => FloatValue(builder.build_float_div(x, y, "")),
            Expr::Modulo(..) => FloatValue(builder.build_float_rem(x, y, "")),
            Expr::Equality(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OEQ, x, y, ""))
            }
            Expr::NotEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::ONE, x, y, ""))
            }
            Expr::GreaterThan(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OGT, x, y, ""))
            }
            Expr::LessThan(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OLT, x, y, ""))
            }
            Expr::GreaterEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OGE, x, y, ""))
            }
            Expr::LessEqual(..) => {
                IntValue(builder.build_float_compare(FloatPredicate::OLE, x, y, ""))
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
        let ty = th.unwrap_or(self.iw.builtins.int64);
        self.iw.builtins.n(n as u64, ty)
    }

    fn resolve_const_float(&self, n: f64, th: Option<FloatType<'a>>) -> FloatValue<'a> {
        let ty = th.unwrap_or(self.iw.builtins.float64);
        self.iw.builtins.flt_n(n, ty)
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
        let struct_def = self.tb.struct_by_name(ty);
        struct_def.as_ref()?;
        let struct_def = struct_def.unwrap();
        let mut val = ty.const_zero();

        match init {
            Some(ai) => match ai {
                AllocInitializer::ByFieldList(init_list) => {
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
                                self.iw.error(CompilerError::new(
                                    fi.value.loc,
                                    Error::InvalidExpression,
                                ));
                                return None;
                            }
                        } else {
                            self.iw.error(CompilerError::new(
                                node.loc,
                                Error::FieldNotFound(fi.field.clone()),
                            ));
                            return None;
                        }
                    }
                }
                AllocInitializer::ByInit(_) => {
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::InitDisallowedInValueTypes,
                    ));
                    return None;
                }
            },
            None => {}
        }

        return Some(BasicValueEnum::StructValue(val));
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
        let pv = alloc_refcounted_type(builder, &self.iw, ty);
        let temp_pv = builder.build_alloca(pv.get_type(), "temp_alloc");
        builder.build_store(temp_pv, pv);
        let ret = builder.build_load(temp_pv, "");
        self.exit.decref_on_exit(temp_pv);

        let struct_def = self.tb.struct_by_name(ty);
        struct_def.as_ref()?;
        let struct_def = struct_def.unwrap();

        match init {
            Some(ai) => match ai {
                AllocInitializer::ByFieldList(init_list) => {
                    if self
                        .tb
                        .find_init_for_type(locals, struct_def.str_ty)
                        .is_some()
                    {
                        self.iw
                            .error(CompilerError::new(node.loc, Error::InitMustBeUsed));
                        return None;
                    }
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
                                self.iw.error(CompilerError::new(
                                    fi.value.loc,
                                    Error::InvalidExpression,
                                ));
                                return None;
                            }
                        } else {
                            self.iw.error(CompilerError::new(
                                node.loc,
                                Error::FieldNotFound(fi.field.clone()),
                            ));
                            return None;
                        }
                    }
                }
                AllocInitializer::ByInit(args) => {
                    if let Some(init_func) = self.tb.find_init_for_type(locals, struct_def.str_ty) {
                        let their_type = init_func.get_type();
                        let mut eval_args: Vec<FunctionCallArgument> =
                            vec![FunctionCallArgument::Value(
                                BasicMetadataValueEnum::PointerValue(pv),
                            )];
                        args.iter().for_each(|arg| {
                            eval_args.push(FunctionCallArgument::Expr(arg.clone()))
                        });
                        if let Some(call_args) = self
                            .build_function_call_args(builder, fd, locals, &eval_args, their_type)
                        {
                            builder.build_call(init_func, &call_args, "");
                        } else {
                            self.iw
                                .error(CompilerError::new(node.loc, Error::InvalidExpression));
                            return None;
                        }
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::FieldNotFound(String::from("init")),
                        ));
                        return None;
                    }
                }
            },
            None => {
                if self
                    .tb
                    .find_init_for_type(locals, struct_def.str_ty)
                    .is_some()
                {
                    self.iw
                        .error(CompilerError::new(node.loc, Error::InitMustBeUsed));
                    return None;
                }
            }
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
                    return self.build_flt_bin_op(builder, ix, iy, &node.payload);
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
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            Multiplication(x, y) | Division(x, y) | Modulo(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, &node.payload);
                }

                self.iw
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
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                }
            }
            GreaterThan(x, y) | GreaterEqual(x, y) | LessThan(x, y) | LessEqual(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, &node.payload);
                }

                self.iw
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            Equality(x, y) | NotEqual(x, y) => {
                let (bx, by) =
                    self.get_binop_args(builder, fd, x.as_ref(), y.as_ref(), locals, type_hint);

                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(PointerValue(ix)), Some(PointerValue(iy))) = (bx, by) {
                    return self.build_ptr_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(PointerValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_ptr_int_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(IntValue(ix)), Some(PointerValue(iy))) = (bx, by) {
                    return self.build_ptr_int_bin_op(builder, iy, ix, &node.payload);
                }

                if let (Some(FloatValue(ix)), Some(FloatValue(iy))) = (bx, by) {
                    return self.build_flt_bin_op(builder, ix, iy, &node.payload);
                }

                self.iw
                    .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                None
            }
            FunctionCall(id, args) => {
                let mut fv: Option<FunctionCallData<'a>> = None;
                if let Some(fbyname) = locals.find_function(id, true) {
                    fv = Some(FunctionCallData::from_function(fbyname));
                } else {
                    let candidate_expr = Expression {
                        loc: node.loc,
                        payload: Expr::Rvalue(crate::ast::Lvalue::Identifier(id.clone())),
                    };
                    if let Some(PointerValue(value)) =
                        self.build_expr(builder, fd, &candidate_expr, locals, type_hint)
                    {
                        if value.get_type().get_element_type().is_function_type() {
                            fv = FunctionCallData::from_pointer(value);
                        }
                    }
                }

                if fv.is_none() {
                    self.iw.error(CompilerError::new(
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
                return if let Some(args) =
                    self.build_function_call_args(builder, fd, locals, &f_args, fv.their_type())
                {
                    self.build_function_call(node, builder, &fv, &args)
                } else {
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::UnexpectedType(Some("callable function".to_owned())),
                    ));
                    None
                };
            }
            MethodCall(mc) => {
                if let Some(this) =
                    self.build_expr(builder, fd, mc.this.as_ref(), locals, type_hint)
                {
                    let mut method_decl: Option<Method<'a>> = None;
                    let mut this_arg: Option<BasicMetadataValueEnum<'a>> = None;
                    let mut matched = false;

                    if let Some(this_type) = self.tb.is_refcounted_basic_type(this.get_type()) {
                        if let Some(let_this_decl) = self.tb.struct_by_name(this_type) {
                            if let Some(let_method_decl) = let_this_decl.method_by_name(&mc.name) {
                                method_decl = Some(let_method_decl);
                                this_arg = Some(BasicMetadataValueEnum::PointerValue(
                                    this.into_pointer_value(),
                                ));
                                matched = true;
                            } else {
                                self.iw.error(CompilerError::new(
                                    node.loc,
                                    Error::IdentifierNotFound(mc.name.clone()),
                                ));
                                return None;
                            }
                        }
                    } else if let Some(this_type) = self.tb.is_value_basic_type(this.get_type()) {
                        if let Some(let_this_decl) = self.tb.struct_by_name(this_type) {
                            if let Some(let_method_decl) = let_this_decl.method_by_name(&mc.name) {
                                method_decl = Some(let_method_decl);
                                this_arg = Some(BasicMetadataValueEnum::StructValue(
                                    this.into_struct_value(),
                                ));
                                matched = true;
                            } else {
                                self.iw.error(CompilerError::new(
                                    node.loc,
                                    Error::IdentifierNotFound(mc.name.clone()),
                                ));
                                return None;
                            }
                        }
                    } else {
                        self.iw.error(CompilerError::new(
                            mc.this.loc,
                            Error::UnexpectedType(Some("value or refcounted type".to_owned())),
                        ));
                        return None;
                    }

                    if !matched {
                        return None;
                    }

                    let method_func = method_decl.unwrap().func;
                    let mut f_args: Vec<FunctionCallArgument> = mc
                        .args
                        .iter()
                        .map(|arg| FunctionCallArgument::Expr(arg.clone()))
                        .collect();
                    f_args.insert(0, FunctionCallArgument::Value(this_arg.unwrap()));

                    return if let Some(args) = self.build_function_call_args(
                        builder,
                        fd,
                        locals,
                        &f_args,
                        method_func.get_type(),
                    ) {
                        let info = FunctionCallData::from_function(method_func);
                        self.build_function_call(node, builder, &info, &args)
                    } else {
                        None
                    };
                } else {
                    None
                }
            }
            Alloc(ty, init) => {
                if let Some(basic_type) = self.tb.llvm_type_by_descriptor(locals, ty) {
                    if let Some(struct_type) = self.tb.is_refcounted_basic_type(basic_type) {
                        return self.alloc_ref_type(builder, locals, struct_type, fd, node, init);
                    } else if let Some(struct_type) = self.tb.is_value_basic_type(basic_type) {
                        return self.alloc_value_type(builder, locals, struct_type, fd, node, init);
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(Some(ty.clone())),
                        ));
                        return None;
                    }
                } else {
                    self.iw.error(CompilerError::new(
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
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(TypeBuilder::descriptor_by_llvm_type(
                                expr.get_type(),
                            )),
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
                                .error(CompilerError::new(node.loc, Error::InvalidExpression));
                            None
                        }
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(TypeBuilder::descriptor_by_llvm_type(
                                expr.get_type(),
                            )),
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
                        self.iw.error(CompilerError::new(node.loc, err));
                        None
                    }
                };
            }
            Cast(e, t) => {
                if let Some(expr) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if let Some(ty) = self.tb.llvm_type_by_descriptor(locals, t) {
                        if let Some(ret) = self.tb.build_cast(builder, expr, ty) {
                            Some(ret)
                        } else {
                            self.iw
                                .error(CompilerError::new(node.loc, Error::InvalidCast));
                            None
                        }
                    } else {
                        self.iw
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
                        if eval_exprs.is_empty() {
                            eval_exprs.push(eval);
                        } else if eval.get_type() != eval_exprs[0].get_type() {
                            self.iw.error(CompilerError::new(
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
                let arr_ptr = builder.build_alloca(arr_ty, "");
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
                let tuple_struct_alloca = builder.build_alloca(tuple_struct_type, "");
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
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::RefTypeInValTypeForbidden,
                    ));
                    return None;
                }

                return Some(BasicValueEnum::StructValue(tuple_struct_value));
            }
            SizeofVar(e) => self
                .build_expr(builder, fd, e.as_ref(), locals, type_hint)
                .map(|expr| BasicValueEnum::IntValue(self.tb.sizeof(expr.get_type()))),
            SizeofTy(ident) => {
                return if let Some(ty) = self.tb.llvm_type_by_descriptor(locals, ident) {
                    if let Some(struct_type) = self.tb.is_refcounted_basic_type(ty) {
                        Some(BasicValueEnum::IntValue(
                            self.tb.sizeof(BasicTypeEnum::StructType(struct_type)),
                        ))
                    } else {
                        Some(BasicValueEnum::IntValue(self.tb.sizeof(ty)))
                    }
                } else {
                    self.iw.error(CompilerError::new(
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
                        self.iw.error(CompilerError::new(node.loc, err));
                        None
                    }
                };
            }
            Deref(e) => {
                if let Some(ev) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if self.tb.is_refcounted_basic_type(ev.get_type()).is_some() {
                        self.iw.error(CompilerError::new(
                            e.loc,
                            Error::UnexpectedType(Some("refcounted type".to_owned())),
                        ));
                        None
                    } else if let PointerValue(pv) = ev {
                        return Some(builder.build_load(pv, ""));
                    } else {
                        self.iw.error(CompilerError::new(
                            e.loc,
                            Error::UnexpectedType(Some("refcounted type".to_owned())),
                        ));
                        return None;
                    }
                } else {
                    self.iw.error(CompilerError::new(
                        e.loc,
                        Error::UnexpectedType(Some("refcounted type".to_owned())),
                    ));
                    None
                }
            }
        }
    }
}
