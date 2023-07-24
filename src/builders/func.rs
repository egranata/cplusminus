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

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    types::FunctionType,
    values::{
        AnyValue, BasicValueEnum, FunctionValue, InstructionOpcode, InstructionValue, PointerValue,
    },
};

use crate::{
    ast::{
        FunctionArgument, FunctionDecl, FunctionDefinition, FunctionTypeDescriptor, TypeDescriptor,
    },
    bom::function::FunctionBomEntry,
    codegen::structure::Structure,
    err::{CompilerError, CompilerWarning, Error, Warning},
    iw::CompilerCore,
    mangler::{mangle_function_name, mangle_method_name},
};

use super::{
    refcount::insert_decref_assume_refcounted,
    scope::{Scope, ScopeObject, VarInfo},
    stmt::StatementBuilder,
    ty::TypeBuilder,
};

#[derive(Clone, Copy, Debug, Default)]
pub struct FunctionBuilderOptions {
    extrn: bool,
    global: bool,
    want_mangle: bool,
    export: bool,
}

impl FunctionBuilderOptions {
    pub fn global(&mut self, g: bool) -> &mut Self {
        self.global = g;
        self
    }

    pub fn extrn(&mut self, e: bool) -> &mut Self {
        self.extrn = e;
        self
    }

    pub fn mangle(&mut self, m: bool) -> &mut Self {
        self.want_mangle = m;
        self
    }

    pub fn export(&mut self, e: bool) -> &mut Self {
        self.export = e;
        self
    }

    pub fn commit(&mut self) -> Self {
        *self
    }
}

pub struct FunctionBuilder<'a> {
    iw: CompilerCore<'a>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(iw: CompilerCore<'a>) -> Self {
        Self { iw }
    }
}

pub fn is_terminator_instruction(iv: InstructionValue) -> bool {
    matches!(
        iv.get_opcode(),
        inkwell::values::InstructionOpcode::Br
            | inkwell::values::InstructionOpcode::Return
            | inkwell::values::InstructionOpcode::Unreachable
    )
}

pub fn is_block_terminated(blk: Option<BasicBlock>) -> bool {
    if let Some(blk) = blk {
        blk.get_last_instruction()
            .map_or(false, is_terminator_instruction)
    } else {
        false
    }
}

pub struct FunctionExitData<'a> {
    pub ret_alloca: Option<PointerValue<'a>>,
    pub allocas_block: BasicBlock<'a>,
    pub exit_block: BasicBlock<'a>,
    pub need_decref: Rc<RefCell<Vec<PointerValue<'a>>>>,
}

pub enum AllocaInitialValue<'a> {
    Zero,
    Undef,
    Val(BasicValueEnum<'a>),
}

impl<'a> FunctionExitData<'a> {
    pub fn create_alloca<T: inkwell::types::BasicType<'a> + Copy>(
        &self,
        bldr: &Builder<'a>,
        ty: T,
        name: Option<&str>,
        val: Option<AllocaInitialValue<'a>>,
    ) -> PointerValue<'a> {
        let blk = bldr.get_insert_block().unwrap();
        bldr.position_at(
            self.allocas_block,
            &self.allocas_block.get_first_instruction().unwrap(),
        );
        // this alloca is whitelisted because it is the bulk of create_alloca behind the scenes
        let pv = bldr.build_alloca(ty, name.unwrap_or(""));
        if let Some(val) = val {
            let ty = ty.as_basic_type_enum();
            match val {
                AllocaInitialValue::Zero => {
                    bldr.build_store(pv, ty.const_zero());
                }
                AllocaInitialValue::Undef => {
                    bldr.build_store(pv, TypeBuilder::undef_for_type(ty));
                }
                AllocaInitialValue::Val(bv) => {
                    bldr.build_store(pv, bv);
                }
            }
        }
        bldr.position_at_end(blk);
        pv
    }
}

impl<'a> FunctionExitData<'a> {
    pub fn decref_on_exit(&self, pv: PointerValue<'a>) {
        self.need_decref.borrow_mut().push(pv);
    }

    pub fn undecref_on_exit(&self, pv: PointerValue<'a>) {
        let mut ndr = self.need_decref.borrow_mut();
        loop {
            let mut any_deleted = false;
            for i in 0..ndr.len() {
                unsafe {
                    let pvi = ndr.get_unchecked(i);
                    if *pvi == pv {
                        ndr.remove(i);
                        any_deleted = true;
                        break;
                    }
                }
            }
            if !any_deleted {
                break;
            };
        }
    }
}

impl<'a> FunctionBuilder<'a> {
    fn build_function_type(
        &self,
        scope: &Scope<'a>,
        fd: &FunctionDecl,
    ) -> Option<FunctionType<'a>> {
        let tb = TypeBuilder::new(self.iw.clone());
        tb.function_type_for_descriptor(scope, &fd.ty)
    }

    fn decref_locals(&self, builder: &Builder<'a>, vc: &FunctionExitData<'a>) {
        for vi in vc.need_decref.borrow().iter() {
            let ptr_val_type = vi.get_type().get_element_type();
            let tb = TypeBuilder::new(self.iw.clone());
            if tb.is_refcounted_any_type(ptr_val_type).is_some() {
                let name = format!(
                    "decref_load_{}",
                    vi.get_name().to_str().unwrap_or("default")
                );
                let load_vi = builder.build_load(*vi, &name);
                insert_decref_assume_refcounted(&self.iw, builder, load_vi);
            }
        }
    }

    fn build_body(&self, func: FunctionValue<'a>, fd: &FunctionDefinition) {
        let entry = self.iw.context.append_basic_block(func, "entry");
        let body = self.iw.context.append_basic_block(func, "body");
        let builder = self.iw.context.create_builder();
        builder.position_at_end(entry);

        let ret_alloca: Option<PointerValue<'a>>;

        let locals = self.build_argument_allocas(func, &builder, fd);
        if let Some(ret_ty) = func.get_type().get_return_type() {
            // this alloca is whitelisted because it is created at function entry
            ret_alloca = Some(builder.build_alloca(ret_ty, "ret_alloca"));
            builder.build_store(ret_alloca.unwrap(), TypeBuilder::undef_for_type(ret_ty));
        } else {
            ret_alloca = None;
        }

        let exit_block = self.iw.context.append_basic_block(func, "exit");

        let exit = FunctionExitData {
            ret_alloca,
            allocas_block: entry,
            exit_block,
            need_decref: Rc::new(RefCell::new(Vec::new())),
        };

        builder.build_unconditional_branch(body);
        builder.position_at_end(body);

        let sb = StatementBuilder::new(self.iw.clone(), &exit);
        sb.build_stmt(&builder, fd, &fd.body, &locals, func, None);

        self.purge_unreachables(func, &exit);

        builder.position_at_end(exit_block);
        if let Some(ret_alloca) = ret_alloca {
            let ret_val = builder.build_load(ret_alloca, "ret");
            self.decref_locals(&builder, &exit);
            builder.build_return(Some(&ret_val));
        } else {
            self.decref_locals(&builder, &exit);
            builder.build_return(None);
        }

        self.build_failsafe_returns(func, &builder, exit_block);
    }

    fn build_argument_allocas(
        &self,
        func: FunctionValue<'a>,
        builder: &Builder<'a>,
        fd: &FunctionDefinition,
    ) -> Scope<'a> {
        let ret: Rc<ScopeObject<'_>> = ScopeObject::child(&self.iw.globals);
        for i in 0..func.get_params().len() {
            let param_name = &fd.decl.args[i].name;
            let param_rw = fd.decl.args[i].rw;
            let param_value = func.get_nth_param(i as u32).unwrap();
            let param_type = param_value.get_type();
            // this alloca is whitelisted because it does not participate in exit deallocation
            let alloca = builder.build_alloca(param_type, param_name);
            builder.build_store(alloca, param_value);
            ret.insert_variable(
                param_name,
                VarInfo::new(fd.decl.loc, param_name.clone(), alloca, param_rw),
                false,
            );
        }

        ret
    }

    fn build_failsafe_returns(
        &self,
        func: FunctionValue<'a>,
        builder: &Builder<'a>,
        exit_block: BasicBlock<'a>,
    ) {
        for bb in func.get_basic_blocks() {
            if !is_block_terminated(Some(bb)) {
                builder.position_at_end(bb);
                builder.build_unconditional_branch(exit_block);
            }
        }
    }

    fn purge_unreachables(&self, func: FunctionValue<'a>, vc: &FunctionExitData<'a>) {
        for bb in func.get_basic_blocks() {
            let mut found_terminal = false;
            let mut instr: Option<InstructionValue<'a>> = bb.get_first_instruction();
            loop {
                if instr.is_none() {
                    break;
                };
                let iv = instr.unwrap();
                instr = iv.get_next_instruction();

                if found_terminal {
                    if iv.get_opcode() == InstructionOpcode::Alloca {
                        let pv = iv.as_any_value_enum().into_pointer_value();
                        vc.undecref_on_exit(pv);
                    }
                    iv.erase_from_basic_block();
                } else if is_terminator_instruction(iv) {
                    found_terminal = true;
                }
            }
        }
    }

    fn check_arg_names_unique(&self, args: &[FunctionArgument]) -> bool {
        let mut seen_args = HashMap::new();

        for arg in args {
            if seen_args.contains_key(&arg.name) {
                self.iw.error(CompilerError::new(
                    arg.loc,
                    Error::DuplicateArgumentName(arg.name.clone()),
                ));
            } else {
                seen_args.insert(arg.name.clone(), arg.loc);
            }
        }

        seen_args.len() == args.len()
    }

    fn declare_function(
        &self,
        scope: &Scope<'a>,
        fd: &FunctionDecl,
        opts: FunctionBuilderOptions,
    ) -> Option<FunctionValue<'a>> {
        let llvm_func_name = if opts.extrn || !opts.want_mangle {
            fd.name.clone()
        } else {
            mangle_function_name(fd)
        };
        if !self.check_arg_names_unique(&fd.args) {
            None
        } else if let Some(func_ty) = self.build_function_type(scope, fd) {
            let func = self.iw.module.add_function(&llvm_func_name, func_ty, None);
            scope.insert_function(&fd.name, func, true);
            Some(func)
        } else {
            self.iw
                .error(CompilerError::new(fd.loc, Error::UnexpectedType(None)));
            None
        }
    }

    fn build_function(
        &self,
        scope: &Scope<'a>,
        fd: &FunctionDefinition,
    ) -> Option<FunctionValue<'a>> {
        if let Some(func) = scope.find_function(&fd.decl.name, true) {
            self.build_body(func, fd);
            Some(func)
        } else {
            self.iw
                .error(CompilerError::new(fd.decl.loc, Error::UnexpectedType(None)));
            None
        }
    }

    pub fn compile(
        &self,
        scope: &Scope<'a>,
        func: &FunctionDefinition,
        opts: FunctionBuilderOptions,
    ) -> Option<FunctionValue<'a>> {
        self.declare(scope, &func.decl, opts)?;
        self.build(scope, func)
    }

    pub fn build(&self, scope: &Scope<'a>, func: &FunctionDefinition) -> Option<FunctionValue<'a>> {
        self.build_function(scope, func)
    }

    pub fn declare(
        &self,
        scope: &Scope<'a>,
        func: &FunctionDecl,
        opts: FunctionBuilderOptions,
    ) -> Option<FunctionValue<'a>> {
        let ret = self.declare_function(scope, func, opts);

        if opts.extrn {
            for arg in &func.args {
                if arg.explicit_rw {
                    self.iw.warning(CompilerWarning::new(
                        arg.loc,
                        Warning::MutabilityArgInExternFunction,
                    ));
                }
            }
        }

        if let Some(fv) = ret {
            if opts.export {
                let bom_entry = FunctionBomEntry::new(&func.name, fv);
                self.iw.bom.borrow_mut().functions.push(bom_entry);
            }
        }

        ret
    }

    pub fn declare_method(
        &self,
        scope: &Scope<'a>,
        fd: &FunctionDefinition,
        self_decl: &Structure<'a>,
        export: bool,
    ) -> (FunctionDecl, Option<FunctionValue<'a>>) {
        let fqn = mangle_method_name(fd, &self_decl.name);
        let self_tyd = TypeDescriptor::Name(self_decl.name.clone());
        let self_arg = FunctionArgument {
            loc: fd.decl.loc,
            name: "self".to_owned(),
            ty: self_tyd,
            rw: false,
            explicit_rw: false,
        };
        let mut new_args = vec![self_arg];
        new_args.extend_from_slice(&fd.decl.args);
        let new_arg_types: Vec<TypeDescriptor> =
            new_args.iter().map(|arg| arg.ty.clone()).collect();
        let ret_type = if let TypeDescriptor::Function(ftd) = &fd.decl.ty {
            &ftd.ret
        } else {
            panic!("unable to infer return type")
        };

        let ftd = FunctionTypeDescriptor::new(new_arg_types, ret_type.clone(), false);
        let fn_type = TypeDescriptor::Function(ftd);

        let new_decl = FunctionDecl {
            loc: fd.decl.loc,
            name: fqn,
            args: new_args,
            ty: fn_type,
        };

        let opts = FunctionBuilderOptions::default()
            .extrn(false)
            .global(true)
            .mangle(false)
            .export(export)
            .commit();

        let fv = self.declare(scope, &new_decl, opts);
        (new_decl, fv)
    }

    pub fn define_method(
        &self,
        scope: &Scope<'a>,
        fd: &FunctionDefinition,
        func_decl: &FunctionDecl,
    ) -> Option<FunctionValue<'a>> {
        let new_def = FunctionDefinition {
            decl: func_decl.clone(),
            body: fd.body.clone(),
            export: false,
        };

        self.build(scope, &new_def)
    }
}
