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

#[cfg(test)]
pub mod test;

pub mod ast;
pub mod builders;
pub mod codegen;
pub mod err;
pub mod iw;
pub mod jit;
pub mod mangler;
pub mod parser;

use std::path::Path;

use crate::iw::Input;
use inkwell::{context::Context, execution_engine::JitFunction};
use iw::CompilerOptions;

use clap::Parser;
#[derive(Clone, Parser, Debug)]
#[command(author, version, about="The C± language", long_about = None)]
struct Args {
    #[arg(short)]
    dump: bool,
    #[arg(short)]
    output: Option<String>,
    #[arg(short = 'O', default_value_t = false)]
    optimize: bool,
    #[arg(long, required = false, default_value = "x86_64-pc-linux-gnu")]
    triple: String,
    #[arg(required = true)]
    input: String,
    #[arg(long, default_value_t = false)]
    instrument_refcount: bool,
    #[arg(long = "Werr", default_value_t = false)]
    warn_as_err: bool,
    #[arg(short = 'l', long = "link")]
    link_extras: Vec<String>,
}

impl Args {
    fn to_codegen_options(&self) -> CompilerOptions {
        CompilerOptions {
            warn_as_err: self.warn_as_err,
            instrument_refcount: self.instrument_refcount,
            link_extras: self.link_extras.clone(),
        }
    }
}

pub fn main() {
    let args = Args::parse();

    let llvm = Context::create();
    let input = Input::from_file(Path::new(&args.input));
    let options = args.to_codegen_options();
    let triple = args.triple;
    let iwell = iw::CompilerCore::new(&llvm, &triple, &input, options);
    let ok = iwell.compile();

    if ok {
        iwell.display_diagnostics();

        if args.optimize {
            iwell.run_passes();
        }

        if args.dump {
            iwell.module.print_to_stderr();
        }

        if let Some(out) = args.output {
            iwell.dump(&out);
        } else {
            type MainFunc = unsafe extern "C" fn() -> u64;
            let main: Option<JitFunction<MainFunc>> =
                jit::get_runnable_function(&iwell, "main", args.optimize);
            if let Some(main) = main {
                let ret = unsafe { main.call() };
                println!("main() returned {ret}");
            } else {
                println!("unable to find main function");
            }
        }
    } else {
        iwell.display_diagnostics();
    }
}
