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
pub mod bom;
pub mod builders;
pub mod codegen;
pub mod driver;
pub mod err;
pub mod iw;
pub mod jit;
pub mod mangler;
pub mod parser;

use std::path::PathBuf;

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
    inputs: Vec<String>,
    #[arg(long, default_value_t = false)]
    instrument_refcount: bool,
    #[arg(long = "Werr", default_value_t = false)]
    warn_as_err: bool,
    #[arg(short = 'l', long = "link")]
    link_extras: Vec<String>,
    #[arg(long = "bom")]
    bom: bool,
    #[arg(short = 'g')]
    debug: bool,
}

impl Args {
    fn to_codegen_options(&self) -> CompilerOptions {
        CompilerOptions {
            triple: self.triple.clone(),
            warn_as_err: self.warn_as_err,
            instrument_refcount: self.instrument_refcount,
            link_extras: self.link_extras.clone(),
            dump_ir_text: self.dump,
            dump_bom: self.bom,
            optimize: self.optimize,
            debug: self.debug,
        }
    }
}

pub fn main() {
    let args = Args::parse();

    let options = args.to_codegen_options();
    let inputs: Vec<PathBuf> = args.inputs.iter().map(PathBuf::from).collect();

    if args.optimize && args.debug {
        eprintln!("cannot generate debug info in optimized builds");
        std::process::exit(1);
    }

    if inputs.len() == 1 && args.output.is_none() {
        let jit_result = driver::run_jit(&inputs[0], &options);
        match jit_result.result {
            Ok(ret) => println!("main returned {ret}"),
            Err(msg) => println!("jit error: {msg}"),
        }
    } else if args.output.is_none() {
        let _ = driver::build_objects(&inputs, options);
    } else {
        let output = PathBuf::from(args.output.unwrap());
        let _ = driver::build_aout(&inputs, output, options);
    }
}
