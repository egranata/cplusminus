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

use either::Either;
use inkwell::{
    builder::Builder,
    types::{BasicTypeEnum, FunctionType, IntType},
    values::{
        BasicMetadataValueEnum, BasicValueEnum, CallableValue, FunctionValue, IntValue,
        PointerValue,
    },
    IntPredicate,
};

use crate::{
    ast::{Expr, Expression, FunctionDefinition},
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

use super::{func::FunctionExitData, var::LocalVariables};

pub struct ExpressionBuilder<'a, 'b> {
    iw: CompilerCore<'a>,
    tb: TypeBuilder<'a>,
    lvb: LvalueBuilder<'a, 'b>,
    exit: &'b FunctionExitData<'a>,
}

struct FunctionCallData<'a> {
    dest: CallableValue<'a>,
    dest_src: Either<FunctionValue<'a>, PointerValue<'a>>,
    argc: usize,
    vararg: bool,
    args: Vec<BasicMetadataValueEnum<'a>>,
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
            args: self.args.clone(),
        }
    }
}

impl<'a> FunctionCallData<'a> {
    fn from_function(f: FunctionValue<'a>, args: Vec<BasicMetadataValueEnum<'a>>) -> Self {
        Self {
            dest: CallableValue::from(f),
            dest_src: Either::Left(f),
            argc: f.count_params() as usize,
            vararg: f.get_type().is_var_arg(),
            args: args.clone(),
        }
    }

    fn from_pointer(p: PointerValue<'a>, args: Vec<BasicMetadataValueEnum<'a>>) -> Option<Self> {
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
                args: args.clone(),
            })
        } else {
            None
        }
    }

    fn check_arg_size_match(&self) -> bool {
        self.args.len() == self.argc || self.vararg
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
    ) -> Option<BasicValueEnum<'a>> {
        if !info.check_arg_size_match() {
            self.iw.error(CompilerError::new(
                node.loc,
                Error::ArgCountMismatch(info.argc, info.args.len()),
            ));
            return None;
        }

        if let Some(obj) = builder
            .build_call(info.clone().dest, &info.args, "")
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
        locals: &LocalVariables<'a>,
        args: &[Expression],
        their_type: FunctionType<'a>,
    ) -> Option<Vec<BasicMetadataValueEnum<'a>>> {
        let mut aargs: Vec<BasicMetadataValueEnum> = vec![];
        for (idx, arg) in args.iter().enumerate() {
            let type_hint = if their_type.get_param_types().len() > idx {
                Some(their_type.get_param_types()[idx])
            } else {
                None
            };
            if let Some(aarg) = self.build_expr(builder, fd, arg, locals, type_hint) {
                aargs.push(BasicMetadataValueEnum::from(aarg));
            } else {
                self.iw
                    .error(CompilerError::new(arg.loc, Error::InvalidExpression));
                return None;
            }
        }

        Some(aargs)
    }

    fn build_int_arith_bin_op(
        &self,
        builder: &Builder<'a>,
        x: IntValue<'a>,
        y: IntValue<'a>,
        op: &Expr,
    ) -> Option<BasicValueEnum<'a>> {
        Some(BasicValueEnum::IntValue(match op {
            Expr::Addition(..) => builder.build_int_add(x, y, ""),
            Expr::Subtraction(..) => builder.build_int_sub(x, y, ""),
            Expr::Multiplication(..) => builder.build_int_mul(x, y, ""),
            Expr::Division(..) => builder.build_int_unsigned_div(x, y, ""),
            Expr::Modulo(..) => builder.build_int_unsigned_rem(x, y, ""),
            Expr::Equality(..) => builder.build_int_compare(IntPredicate::EQ, x, y, ""),
            Expr::NotEqual(..) => builder.build_int_compare(IntPredicate::NE, x, y, ""),
            Expr::GreaterThan(..) => builder.build_int_compare(IntPredicate::SGT, x, y, ""),
            Expr::LessThan(..) => builder.build_int_compare(IntPredicate::SLT, x, y, ""),
            Expr::GreaterEqual(..) => builder.build_int_compare(IntPredicate::SGE, x, y, ""),
            Expr::LessEqual(..) => builder.build_int_compare(IntPredicate::SLE, x, y, ""),
            _ => panic!(""),
        }))
    }

    pub fn build_expr(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        locals: &LocalVariables<'a>,
        type_hint: Option<BasicTypeEnum<'a>>,
    ) -> Option<BasicValueEnum<'a>> {
        if let Some(val) = self.do_build_expr(builder, fd, node, locals, type_hint) {
            Some(val)
        } else {
            self.iw
                .error(CompilerError::new(node.loc, Error::InvalidExpression));
            None
        }
    }

    fn resolve_const_int(&self, n: i64, th: Option<IntType<'a>>) -> IntValue<'a> {
        let ty = th.unwrap_or(self.iw.builtins.int64);
        self.iw.builtins.n(n as u64, ty)
    }

    fn do_build_expr(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Expression,
        locals: &LocalVariables<'a>,
        type_hint: Option<BasicTypeEnum<'a>>,
    ) -> Option<BasicValueEnum<'a>> {
        use crate::ast::Expr::*;
        use BasicValueEnum::{IntValue, PointerValue};

        match &node.payload {
            ConstInt(n) => {
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
            ConstString(s) => {
                let gv = builder.build_global_string_ptr(s, "");
                Some(PointerValue(gv.as_pointer_value()))
            }
            Addition(x, y) | Subtraction(x, y) => {
                let bx = self.build_expr(builder, fd, x.as_ref(), locals, type_hint);
                let by = self.build_expr(builder, fd, y.as_ref(), locals, type_hint);
                if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    return self.build_int_arith_bin_op(builder, ix, iy, &node.payload);
                }

                if let (Some(PointerValue(px)), Some(IntValue(iy))) = (bx, by) {
                    let ix = builder.build_ptr_to_int(px, self.iw.builtins.int64, "");
                    let st = px.get_type().get_element_type().size_of().unwrap();
                    let iy_sized = builder.build_int_mul(iy, st, "");
                    let ix_inc = self
                        .build_int_arith_bin_op(builder, ix, iy_sized, &node.payload)
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
                let bx = self.build_expr(builder, fd, x.as_ref(), locals, type_hint);
                let by = self.build_expr(builder, fd, y.as_ref(), locals, type_hint);
                return if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    self.build_int_arith_bin_op(builder, ix, iy, &node.payload)
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
                } else {
                    self.iw
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                }
            }
            GreaterThan(x, y)
            | GreaterEqual(x, y)
            | LessThan(x, y)
            | LessEqual(x, y)
            | Equality(x, y)
            | NotEqual(x, y) => {
                let bx = self.build_expr(builder, fd, x.as_ref(), locals, type_hint);
                let by = self.build_expr(builder, fd, y.as_ref(), locals, type_hint);
                return if let (Some(IntValue(ix)), Some(IntValue(iy))) = (bx, by) {
                    self.build_int_arith_bin_op(builder, ix, iy, &node.payload)
                } else {
                    self.iw
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                    None
                };
            }
            PointerFunctionCall(expr, args) => {
                if let Some(PointerValue(pv)) =
                    self.build_expr(builder, fd, expr.as_ref(), locals, type_hint)
                {
                    if !pv.get_type().get_element_type().is_function_type() {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::UnexpectedType(Some("function pointer expected".to_owned())),
                        ));
                        return None;
                    }
                    let their_type = pv.get_type().get_element_type().into_function_type();
                    if let Some(args) =
                        self.build_function_call_args(builder, fd, locals, args, their_type)
                    {
                        if let Some(info) = FunctionCallData::from_pointer(pv, args) {
                            return self.build_function_call(node, builder, &info);
                        } else {
                            self.iw.error(CompilerError::new(
                                node.loc,
                                Error::UnexpectedType(Some("function pointer expected".to_owned())),
                            ));
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            FunctionCall(id, args) => {
                if let Some((_, fv)) = self.iw.funcs.as_ref().borrow().get(id) {
                    if let Some(args) =
                        self.build_function_call_args(builder, fd, locals, args, fv.get_type())
                    {
                        let info = FunctionCallData::from_function(*fv, args);
                        return self.build_function_call(node, builder, &info);
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::IdentifierNotFound(id.clone()),
                        ));
                        None
                    }
                } else {
                    None
                }
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
                    }

                    if !matched {
                        return None;
                    }

                    let method_func = method_decl.unwrap().func;

                    return if let Some(mut args) = self.build_function_call_args(
                        builder,
                        fd,
                        locals,
                        &mc.args,
                        method_func.get_type(),
                    ) {
                        args.insert(0, this_arg.unwrap());
                        let info = FunctionCallData::from_function(method_func, args);
                        self.build_function_call(node, builder, &info)
                    } else {
                        None
                    };
                } else {
                    None
                }
            }
            Alloc(ty) => {
                if let Some(basic_type) = self.tb.llvm_type_by_descriptor(ty) {
                    if let Some(struct_type) = self.tb.is_refcounted_basic_type(basic_type) {
                        let pv = alloc_refcounted_type(builder, &self.iw, struct_type);
                        let temp_pv = builder.build_alloca(pv.get_type(), "temp_alloc");
                        builder.build_store(temp_pv, pv);
                        let ret = builder.build_load(temp_pv, "");
                        self.exit.decref_on_exit(temp_pv);
                        Some(ret)
                    } else if let Some(struct_type) = self.tb.is_value_basic_type(basic_type) {
                        let val = struct_type.const_zero();
                        return Some(BasicValueEnum::StructValue(val));
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
                        let name = format!("load_{}", String::from(lv));
                        Some(builder.build_load(pv.ptr, &name))
                    }
                    Err(err) => {
                        self.iw.error(CompilerError::new(node.loc, err));
                        None
                    }
                };
            }
            Cast(e, t) => {
                if let Some(expr) = self.build_expr(builder, fd, e.as_ref(), locals, type_hint) {
                    if let Some(ty) = self.tb.llvm_type_by_descriptor(t) {
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
                                Error::UnexpectedType(Some(
                                    "not all entries are of the same type".to_owned(),
                                )),
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
            SizeofVar(e) => self
                .build_expr(builder, fd, e.as_ref(), locals, type_hint)
                .map(|expr| BasicValueEnum::IntValue(self.tb.sizeof(expr.get_type()))),
            SizeofTy(ident) => {
                return if let Some(ty) = self.tb.llvm_type_by_descriptor(ident) {
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
                            Error::UnexpectedType(Some("type is not a pointer".to_owned())),
                        ));
                        None
                    } else if let PointerValue(pv) = ev {
                        return Some(builder.build_load(pv, ""));
                    } else {
                        self.iw.error(CompilerError::new(
                            e.loc,
                            Error::UnexpectedType(Some("type is not a pointer".to_owned())),
                        ));
                        return None;
                    }
                } else {
                    self.iw.error(CompilerError::new(
                        e.loc,
                        Error::UnexpectedType(Some("type is not a pointer".to_owned())),
                    ));
                    None
                }
            }
        }
    }
}
