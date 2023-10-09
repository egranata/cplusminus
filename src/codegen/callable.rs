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
    types::FunctionType,
    values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue, PointerValue},
};

use crate::{
    ast::{Expression, FunctionDefinition},
    builders::{
        expr::{ExpressionBuilder, FunctionCallArgument},
        scope::Scope,
    },
    err::{CompilerError, Error},
};

fn build_not_hintable_arg_list<'a, 'b>(
    eb: &ExpressionBuilder<'a, 'b>,
    builder: &Builder<'a>,
    fd: &FunctionDefinition,
    locals: &Scope<'a>,
    args: &[FunctionCallArgument<'a>],
) -> Option<Vec<FunctionCallArgument<'a>>> {
    let mut out: Vec<FunctionCallArgument<'a>> = vec![];
    for arg in args {
        match arg {
            FunctionCallArgument::Expr(e) => {
                if e.payload.is_const_hintable() {
                    out.push(arg.clone());
                } else if let Some(v) = eb.build_expr(builder, fd, e, locals, None) {
                    out.push(FunctionCallArgument::Value(v.into()));
                } else {
                    return None;
                }
            }
            FunctionCallArgument::Value(v) => {
                out.push(FunctionCallArgument::Value(*v));
            }
        }
    }

    Some(out)
}

fn test_overload_candidate<'a>(
    eb: &ExpressionBuilder<'a, '_>,
    builder: &Builder<'a>,
    fd: &FunctionDefinition,
    locals: &Scope<'a>,
    args: &[FunctionCallArgument<'a>],
    candidate: FunctionValue<'a>,
) -> Option<Vec<FunctionCallArgument<'a>>> {
    let candidate_type = candidate.get_type();
    let mut ret_args: Vec<FunctionCallArgument> = vec![];
    for (idx, arg) in args.iter().enumerate() {
        let type_hint = candidate_type.get_param_types().get(idx).copied();

        match arg {
            FunctionCallArgument::Expr(e) => {
                let argv = eb.build_expr(builder, fd, e, locals, type_hint);
                argv?;
                if type_hint.is_some() && argv.unwrap().get_type() != type_hint.unwrap() {
                    return None;
                }
                ret_args.push(FunctionCallArgument::Value(argv.unwrap().into()));
            }
            FunctionCallArgument::Value(v) => {
                if type_hint.is_some() && !eb.tb.arg_type_matches(*v, type_hint.unwrap()) {
                    return None;
                }
                ret_args.push(arg.clone());
            }
        }
    }

    Some(ret_args)
}

#[derive(Clone, Debug)]
pub enum Callable<'a> {
    Fn(FunctionValue<'a>),
    Ptr(PointerValue<'a>, FunctionType<'a>),
}

impl<'a> Callable<'a> {
    pub fn from_function(f: FunctionValue<'a>) -> Self {
        Self::Fn(f)
    }

    pub fn from_pointer(p: PointerValue<'a>) -> Option<Self> {
        let pt = p.get_type().get_element_type();
        if pt.is_function_type() {
            Some(Self::Ptr(p, pt.into_function_type()))
        } else {
            None
        }
    }

    pub fn from_overload_set<'b>(
        eb: &ExpressionBuilder<'a, 'b>,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        locals: &Scope<'a>,
        name: &str,
        args: &[FunctionCallArgument<'a>],
        candidates: &[FunctionValue<'a>],
    ) -> Result<Callable<'a>, crate::err::Error> {
        // first do the very easy thing - can we find one and only one possible candidate
        // by argument count?
        let args = build_not_hintable_arg_list(eb, builder, fd, locals, args);
        if args.is_none() {
            return Err(crate::err::Error::InvalidExpression);
        }
        let args = args.unwrap();

        let len = args.len();
        let step0_filter: Vec<_> = candidates
            .iter()
            .filter(|c| c.count_params() as usize == len)
            .collect();

        if step0_filter.is_empty() {
            // for methods, subtract 1 since there is an implicit "self" argument
            // since we don't overload on free functions for now, this is generally
            // safe to do
            return Err(crate::err::Error::OverloadSetEmptyArgc(
                name.to_owned(),
                len - 1,
            ));
        }
        if step0_filter.len() == 1 {
            let f = *step0_filter[0];
            return Ok(Callable::from_function(f));
        }

        // then try to resolve all constant arguments and see if we end up with one and only one match
        // the idea is that this is mostly stuff of the form foo(3) with overloads like foo(int64), foo(blah)
        // and so it's safe to attempt to construct multiple times
        // one possible step missing (here? elsewhere?) is to apply obvious promotions, so for example
        // let x: int32 = 3
        // foo(x) should probably work for foo(int64), since we promote integers in other contexts
        let mut step1_filter: Vec<(FunctionValue, Vec<FunctionCallArgument>)> = vec![];
        for c in step0_filter {
            let attempt = test_overload_candidate(eb, builder, fd, locals, &args, *c);
            if let Some(fca) = attempt {
                step1_filter.push((*c, fca));
            }
        }

        if step1_filter.is_empty() {
            return Err(crate::err::Error::OverloadSetEmptyArgv(name.to_owned()));
        }
        if step1_filter.len() == 1 {
            let f = step1_filter[0].0;
            return Ok(Callable::from_function(f));
        }

        // if we end up with more than one resolution here it's likely to be a case of
        // foo(3) with foo(int32) vs. foo(int64) and so a way to resolve the overload should always exist
        // by means of the user providing an explicit type; the diagnostic right now is very much suboptimal
        // but it at least exists

        Err(crate::err::Error::OverloadSetAmbiguous(name.to_owned()))
    }

    pub fn callee(&self) -> inkwell::values::CallableValue<'a> {
        use inkwell::values::CallableValue as CV;

        match self {
            Callable::Fn(f) => CV::from(*f),
            Callable::Ptr(p, _) => CV::try_from(*p).unwrap(),
        }
    }

    pub fn is_vararg(&self) -> bool {
        match self {
            Callable::Fn(f) => f.get_type().is_var_arg(),
            Callable::Ptr(_, ft) => ft.is_var_arg(),
        }
    }

    pub fn argc(&self) -> usize {
        match self {
            Callable::Fn(f) => f.count_params() as usize,
            Callable::Ptr(_, ft) => ft.count_param_types() as usize,
        }
    }

    pub fn fn_type(&self) -> FunctionType<'a> {
        match self {
            Callable::Fn(f) => f.get_type(),
            Callable::Ptr(_, ft) => *ft,
        }
    }

    pub fn typecheck_call(&self, args: &[BasicMetadataValueEnum]) -> bool {
        self.is_vararg() || args.len() == self.argc()
    }
}

#[derive(Clone, Debug)]
pub struct Call<'a> {
    target: Callable<'a>,
    args: Vec<BasicMetadataValueEnum<'a>>,
}

impl<'a> Call<'a> {
    pub fn try_build<'b>(
        eb: &ExpressionBuilder<'a, 'b>,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
        locals: &Scope<'a>,
        args: &[FunctionCallArgument<'a>],
        target: Callable<'a>,
    ) -> Option<Call<'a>> {
        let their_type = target.fn_type();

        let mut aargs: Vec<BasicMetadataValueEnum<'a>> = vec![];
        for (idx, arg) in args.iter().enumerate() {
            let type_hint = if their_type.get_param_types().len() > idx {
                Some(their_type.get_param_types()[idx])
            } else {
                None
            };
            match arg {
                FunctionCallArgument::Expr(expr) => {
                    if let Some(aarg) = eb.build_expr(builder, fd, expr, locals, type_hint) {
                        let aarg_type = aarg.get_type();
                        let compat = type_hint.map_or(true, |ft| ft == aarg_type);
                        if compat {
                            aargs.push(BasicMetadataValueEnum::from(aarg));
                        } else {
                            // safe because compat is always true when no type hint is available
                            let exp_type = eb.tb.descriptor_by_llvm_type(type_hint.unwrap());
                            eb.iw.diagnostics.borrow_mut().error(CompilerError::new(
                                expr.loc,
                                Error::UnexpectedType(exp_type.map(|t| format!("{t}"))),
                            ));
                            return None;
                        }
                    } else {
                        eb.iw
                            .diagnostics
                            .borrow_mut()
                            .error(CompilerError::new(expr.loc, Error::InvalidExpression));
                        return None;
                    }
                }
                FunctionCallArgument::Value(val) => aargs.push(*val),
            }
        }

        Some(Call {
            target,
            args: aargs,
        })
    }

    pub fn build_call<'b>(
        &self,
        eb: &ExpressionBuilder<'a, 'b>,
        builder: &Builder<'a>,
        node: &Expression,
    ) -> Option<BasicValueEnum<'a>> {
        if !self.target.typecheck_call(&self.args) {
            eb.iw.diagnostics.borrow_mut().error(CompilerError::new(
                node.loc,
                Error::ArgCountMismatch(self.target.argc(), self.args.len()),
            ));
            return None;
        }

        if let Some(obj) = builder
            .build_call(self.target.callee(), &self.args, "")
            .try_as_basic_value()
            .left()
        {
            let temp_pv = eb.exit.create_alloca(
                builder,
                obj.get_type(),
                Some("temp_func"),
                Some(crate::builders::func::AllocaInitialValue::Zero),
            );
            builder.build_store(temp_pv, obj);
            eb.exit.decref_on_exit(temp_pv);
            Some(obj)
        } else {
            None
        }
    }
}
