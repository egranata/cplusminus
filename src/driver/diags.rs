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

use std::{cell::RefCell, rc::Rc};

use crate::err::{CompilerDiagnostic, CompilerError, CompilerWarning, Error};

#[derive(Clone, Debug)]
pub struct Diagnostics {
    pub data: Vec<CompilerDiagnostic>,
    pub warn_as_err: bool,
    pub diag_file: codespan_reporting::files::SimpleFile<String, String>,
}

impl Diagnostics {
    pub fn new(warn_as_err: bool, input: &crate::iw::Input) -> crate::codegen::MutableOf<Self> {
        Rc::new(RefCell::new(Self {
            data: Default::default(),
            warn_as_err,
            diag_file: input.diag_file.clone(),
        }))
    }

    pub fn error(&mut self, err: CompilerError) {
        self.data.push(CompilerDiagnostic::Error(err))
    }

    pub fn warning(&mut self, warn: CompilerWarning) {
        if self.warn_as_err {
            let err = CompilerError {
                loc: warn.loc,
                err: Error::WarningAsError(warn.warn),
            };
            self.data.push(CompilerDiagnostic::Error(err));
        } else {
            self.data.push(CompilerDiagnostic::Warning(warn))
        }
    }

    pub fn ok(&self) -> bool {
        for diag in &self.data {
            if let CompilerDiagnostic::Error(..) = diag {
                return false;
            }
        }

        true
    }

    fn run_through_diags(&self, writer: &mut dyn codespan_reporting::term::termcolor::WriteColor) {
        use codespan_reporting::diagnostic::Diagnostic;
        use codespan_reporting::diagnostic::Label;

        #[allow(clippy::let_unit_value)]
        let file_id = ();
        let config = codespan_reporting::term::Config::default();

        for diag in self.data.iter() {
            let diagnostic = match diag {
                CompilerDiagnostic::Error(err) => Diagnostic::error()
                    .with_message(format!("{}", err.err))
                    .with_labels(vec![Label::primary(file_id, err.loc.start..err.loc.end)]),
                CompilerDiagnostic::Warning(warn) => {
                    codespan_reporting::diagnostic::Diagnostic::warning()
                        .with_message(format!("{}", warn.warn))
                        .with_labels(vec![Label::primary(file_id, warn.loc.start..warn.loc.end)])
                }
            };

            codespan_reporting::term::emit(writer, &config, &self.diag_file, &diagnostic)
                .expect("<io error>");
        }
    }

    pub fn display_diagnostics(&self) {
        let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
            codespan_reporting::term::termcolor::ColorChoice::Always,
        );
        self.run_through_diags(&mut writer.lock());
    }

    pub fn diagnostics_to_string(&self) -> String {
        #[derive(Default)]
        struct StringStream {
            s: String,
        }
        impl std::io::Write for StringStream {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                if let Ok(str) = String::from_utf8(buf.to_vec()) {
                    self.s = format!("{}{}", self.s, str);
                    Ok(str.len())
                } else {
                    Err(std::io::Error::from(std::io::ErrorKind::InvalidData))
                }
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        impl codespan_reporting::term::termcolor::WriteColor for StringStream {
            fn supports_color(&self) -> bool {
                false
            }

            fn set_color(
                &mut self,
                _: &codespan_reporting::term::termcolor::ColorSpec,
            ) -> std::io::Result<()> {
                Ok(())
            }

            fn reset(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        let mut writer = StringStream::default();

        self.run_through_diags(&mut writer);

        writer.s
    }
}
