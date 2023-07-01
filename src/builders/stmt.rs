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
    basic_block::BasicBlock, builder::Builder, types::BasicTypeEnum, values::FunctionValue,
};

use crate::{
    ast::{FunctionDefinition, IfCondition, Statement},
    builders::{
        lvalue::LvalueBuilder,
        refcount::{insert_decref_if_refcounted, insert_incref_if_refcounted},
        var::{VarContext, VarInfo},
    },
    err::{CompilerError, CompilerWarning, Error, Warning},
    iw::CompilerCore,
};

use super::{
    expr::ExpressionBuilder,
    func::{is_block_terminated, FunctionExitData},
    ty::TypeBuilder,
    var::LocalVariables,
};

pub struct StatementBuilder<'a, 'b> {
    iw: CompilerCore<'a>,
    eb: ExpressionBuilder<'a, 'b>,
    tb: TypeBuilder<'a>,
    lvb: LvalueBuilder<'a, 'b>,
    exit: &'b FunctionExitData<'a>,
}

impl<'a, 'b> StatementBuilder<'a, 'b> {
    pub fn new(iw: CompilerCore<'a>, exit: &'b FunctionExitData<'a>) -> Self {
        Self {
            iw: iw.clone(),
            eb: ExpressionBuilder::new(iw.clone(), exit),
            tb: TypeBuilder::new(iw.clone()),
            lvb: LvalueBuilder::new(iw.clone(), exit),
            exit,
        }
    }

    fn build_if_condition(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &IfCondition,
        locals: &LocalVariables<'a>,
        func: FunctionValue<'a>,
        after: BasicBlock<'a>,
    ) {
        let bb_then = self.iw.context.append_basic_block(func, "then");
        let bb_els = self.iw.context.append_basic_block(func, "els");
        if let Some(expr) = self
            .eb
            .build_expr(builder, fd, node.cond.as_ref(), locals, None)
        {
            if self.tb.is_boolean(expr.get_type()) {
                builder.build_conditional_branch(expr.into_int_value(), bb_then, bb_els);
                builder.position_at_end(bb_then);
                self.build_stmt(builder, fd, &node.body, locals, func);
                if !is_block_terminated(builder.get_insert_block()) {
                    builder.build_unconditional_branch(after);
                }
                builder.position_at_end(bb_els);
            } else {
                self.iw.error(CompilerError::new(
                    node.cond.loc,
                    Error::UnexpectedType(Some(
                        "only boolean values can be used in conditionals".to_owned(),
                    )),
                ));
            }
        } else {
            self.iw
                .error(CompilerError::new(node.cond.loc, Error::InvalidExpression));
        }
    }

    fn warn_on_unwritten_locals(&self, vc: &VarContext) {
        for vi in vc.storage.borrow().values() {
            if vi.rw && !*vi.written.borrow() {
                self.iw.warning(CompilerWarning::new(
                    vi.loc,
                    Warning::MutableValueNeverWrittenTo(vi.name.clone()),
                ));
            }
        }
    }

    pub fn build_stmt(
        &self,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        node: &Statement,
        locals: &LocalVariables<'a>,
        func: FunctionValue<'a>,
    ) {
        use crate::ast::Stmt::*;

        match &node.payload {
            Block(block) => {
                let block_locals = VarContext::child(locals);
                for node in block {
                    self.build_stmt(builder, fd, node, &block_locals, func);
                }
                self.warn_on_unwritten_locals(&block_locals);
            }
            Return(expr) => {
                if expr.is_some() != func.get_type().get_return_type().is_some() {
                    self.iw
                        .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                } else if expr.is_none() {
                    builder.build_unconditional_branch(self.exit.exit_block);
                    return;
                } else {
                    let expr = expr.as_ref().unwrap();
                    let type_hint = func.get_type().get_return_type();
                    if let Some(value) = self.eb.build_expr(builder, fd, expr, locals, type_hint) {
                        if self.tb.is_same_type(
                            value.get_type(),
                            self.exit.ret_alloca.unwrap().get_type().get_element_type(),
                        ) {
                            if self.tb.is_refcounted_basic_type(value.get_type()).is_some() {
                                let tmp = builder.build_alloca(value.get_type(), "temp_ret");
                                builder.build_store(tmp, value);
                                insert_incref_if_refcounted(&self.iw, builder, value);
                            }
                            builder.build_store(self.exit.ret_alloca.unwrap(), value);
                            builder.build_unconditional_branch(self.exit.exit_block);
                        } else {
                            self.iw
                                .error(CompilerError::new(node.loc, Error::UnexpectedType(None)));
                        }
                    } else {
                        self.iw
                            .error(CompilerError::new(expr.loc, Error::InvalidExpression));
                    }
                }
            }
            Decref(expr) => {
                if let Some(value) = self.eb.build_expr(builder, fd, expr.as_ref(), locals, None) {
                    if self.tb.is_refcounted_basic_type(value.get_type()).is_some() {
                        insert_decref_if_refcounted(&self.iw, builder, value);
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::TypeNotRefcounted(TypeBuilder::descriptor_by_llvm_type(
                                value.get_type(),
                            )),
                        ));
                    }
                }
            }
            VarDecl(var) => {
                if var.ty.is_none() && var.val.is_none() {
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::UnresolvedVariableDeclaration,
                    ));
                    return;
                }

                let value = if let Some(val) = &var.val {
                    let type_hint = if let Some(td) = var.ty.as_ref() {
                        self.tb.llvm_type_by_descriptor(td)
                    } else {
                        None
                    };
                    let maybe_val = self.eb.build_expr(builder, fd, val, locals, type_hint);
                    if let Some(v) = maybe_val {
                        v
                    } else {
                        self.iw
                            .error(CompilerError::new(val.loc, Error::InvalidExpression));
                        return;
                    }
                } else if !var.rw {
                    self.iw
                        .error(CompilerError::new(node.loc, Error::LetMustBeInitialized));
                    return;
                } else if let Some(decl_ty) =
                    self.tb.llvm_type_by_descriptor(var.ty.as_ref().unwrap())
                {
                    decl_ty.const_zero()
                } else {
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::TypeNotFound(var.ty.clone().unwrap()),
                    ));
                    return;
                };

                let decl_ty = if let Some(var_ty) = &var.ty {
                    let maybe_type = self.tb.llvm_type_by_descriptor(var_ty);
                    if let Some(t) = maybe_type {
                        t
                    } else {
                        self.iw.error(CompilerError::new(
                            node.loc,
                            Error::TypeNotFound(var_ty.clone()),
                        ));
                        return;
                    }
                } else {
                    value.get_type()
                };

                if value.get_type() != decl_ty {
                    let val_ty_td = TypeBuilder::descriptor_by_llvm_type(value.get_type()).unwrap();
                    let decl_ty_td = TypeBuilder::descriptor_by_llvm_type(decl_ty).unwrap();
                    self.iw.error(CompilerError::new(
                        node.loc,
                        Error::InvalidTypeSpecifier(decl_ty_td, val_ty_td),
                    ));
                    return;
                }

                let alloca = builder.build_alloca(decl_ty, &var.name);
                builder.build_store(alloca, value);
                insert_incref_if_refcounted(&self.iw, builder, value);
                self.exit.decref_on_exit(alloca);
                locals.insert(
                    &var.name,
                    VarInfo::new(node.loc, var.name.clone(), alloca, var.rw),
                    true,
                );
            }
            Expression(e) => {
                if let Some(obj) = self.eb.build_expr(builder, fd, e.as_ref(), locals, None) {
                    let temp_rv = builder.build_alloca(obj.get_type(), "temp_stmt_expr");
                    builder.build_store(temp_rv, obj);
                }
            }
            Assignment(name, expr) => {
                let tgt_pv = self.lvb.build_lvalue(builder, fd, name, locals);
                match tgt_pv {
                    Ok(pv) => {
                        if pv.rw {
                            let type_hint =
                                BasicTypeEnum::try_from(pv.ptr.get_type().get_element_type())
                                    .unwrap();
                            let new_val = self.eb.build_expr(
                                builder,
                                fd,
                                expr.as_ref(),
                                locals,
                                Some(type_hint),
                            );
                            if new_val.is_none() {
                                self.iw
                                    .error(CompilerError::new(expr.loc, Error::InvalidExpression));
                                return;
                            }
                            let new_value = new_val.unwrap();
                            if self.tb.is_same_type(
                                new_value.get_type(),
                                pv.ptr.get_type().get_element_type(),
                            ) {
                                let old_value = builder.build_load(pv.ptr, "");
                                insert_decref_if_refcounted(&self.iw, builder, old_value);
                                insert_incref_if_refcounted(&self.iw, builder, new_value);
                                builder.build_store(pv.ptr, new_value);
                                if let Some(var) = pv.var {
                                    *var.written.borrow_mut() = true;
                                }
                            } else {
                                self.iw.error(CompilerError::new(
                                    node.loc,
                                    Error::UnexpectedType(None),
                                ));
                            }
                        } else {
                            self.iw.error(CompilerError::new(
                                node.loc,
                                Error::ReadOnlyIdentifier(String::from(name)),
                            ))
                        }
                    }
                    Err(err) => {
                        self.iw.error(CompilerError::new(node.loc, err));
                    }
                }
            }
            If(stmt) => {
                let bb_after = self.iw.context.append_basic_block(func, "after");
                self.build_if_condition(builder, fd, &stmt.base, locals, func, bb_after);
                for cond in &stmt.alts {
                    self.build_if_condition(builder, fd, cond, locals, func, bb_after);
                }
                if let Some(otherwise) = &stmt.othw {
                    self.build_stmt(builder, fd, otherwise.as_ref(), locals, func);
                    if !is_block_terminated(builder.get_insert_block()) {
                        builder.build_unconditional_branch(bb_after);
                    }
                    builder.position_at_end(bb_after);
                } else {
                    builder.build_unconditional_branch(bb_after);
                    builder.position_at_end(bb_after);
                }
            }
            While(wh) => {
                let bb_check = self.iw.context.append_basic_block(func, "check");
                let bb_body = self.iw.context.append_basic_block(func, "do");
                let bb_after = self.iw.context.append_basic_block(func, "after");
                let ran_once = builder.build_alloca(self.iw.builtins.bool, "");
                builder.build_store(ran_once, self.iw.builtins.zero(self.iw.builtins.bool));
                builder.build_unconditional_branch(bb_check);
                builder.position_at_end(bb_check);
                if let Some(ec) = self
                    .eb
                    .build_expr(builder, fd, wh.cond.as_ref(), locals, None)
                {
                    if !self.tb.is_boolean(ec.get_type()) {
                        return self.iw.error(CompilerError::new(
                            wh.cond.loc,
                            Error::UnexpectedType(Some(
                                "only boolean values can be used in conditionals".to_owned(),
                            )),
                        ));
                    }
                    builder.build_conditional_branch(ec.into_int_value(), bb_body, bb_after);
                    builder.position_at_end(bb_body);
                    builder.build_store(ran_once, self.iw.builtins.one(self.iw.builtins.bool));
                    self.build_stmt(builder, fd, wh.body.as_ref(), locals, func);
                    if !is_block_terminated(builder.get_insert_block()) {
                        builder.build_unconditional_branch(bb_check);
                    }
                    builder.position_at_end(bb_after);
                    if let Some(otherwise) = &wh.els {
                        let bb_dootherwise =
                            self.iw.context.append_basic_block(func, "dootherwise");
                        let bb_alldone = self.iw.context.append_basic_block(func, "alldone");
                        builder.build_conditional_branch(
                            builder.build_load(ran_once, "").into_int_value(),
                            bb_alldone,
                            bb_dootherwise,
                        );
                        builder.position_at_end(bb_dootherwise);
                        self.build_stmt(builder, fd, otherwise.as_ref(), locals, func);
                        if !is_block_terminated(builder.get_insert_block()) {
                            builder.build_unconditional_branch(bb_alldone);
                        }
                        builder.position_at_end(bb_alldone);
                    }
                } else {
                    self.iw
                        .error(CompilerError::new(wh.cond.loc, Error::InvalidExpression))
                }
            }
            Assert(expr) => {
                if let Some(cond) = self.eb.build_expr(builder, fd, expr.as_ref(), locals, None) {
                    if self.tb.is_boolean(cond.get_type()) {
                        let bb_check = self.iw.context.append_basic_block(func, "check");
                        let bb_trap = self.iw.context.append_basic_block(func, "do_trap");
                        let bb_ok = self.iw.context.append_basic_block(func, "ok");
                        builder.build_unconditional_branch(bb_check);
                        builder.position_at_end(bb_check);
                        builder.build_conditional_branch(cond.into_int_value(), bb_ok, bb_trap);
                        builder.position_at_end(bb_trap);
                        let llvmtrap = self.iw.module.get_function("llvm.trap");
                        builder.build_call(llvmtrap.unwrap(), &[], "");
                        builder.position_at_end(bb_ok);
                    } else {
                        self.iw.error(CompilerError::new(
                            expr.loc,
                            Error::UnexpectedType(Some(
                                "only boolean values can be used in conditionals".to_owned(),
                            )),
                        ));
                    }
                } else {
                    self.iw
                        .error(CompilerError::new(expr.loc, Error::InvalidExpression))
                }
            }
        }
    }
}
