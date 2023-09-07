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

use std::fmt::Display;

use crate::ast::{TokenSpan, TypeDescriptor};

#[derive(Clone, Debug)]
pub enum Error {
    IdentifierNotFound(String),
    TypeNotFound(TypeDescriptor),
    TypeNotRefcounted(Option<TypeDescriptor>),
    UnexpectedType(Option<String>),
    ArgCountMismatch(usize, usize),
    OverloadSetEmptyArgc(String, usize),
    OverloadSetEmptyArgv(String),
    OverloadSetAmbiguous(String),
    InvalidExpression,
    InternalError(String),
    ParseError(String),
    RecursiveTypeForbidden(String),
    UnexpectedState(String),
    ReadOnlyIdentifier(String),
    DotAccessInvalid,
    FieldNotFound(String),
    InvalidCast,
    ReservedIdentifier(String),
    DuplicatedStructMember(String),
    InitDisallowedInValueTypes,
    DeallocDisallowedInValueTypes,
    InitMustBeUsed,
    WarningAsError(Warning),
    InvalidTypeSpecifier(TypeDescriptor, TypeDescriptor),
    DuplicateArgumentName(String),
    UnresolvedVariableDeclaration,
    LetMustBeInitialized,
    RefTypeInValTypeForbidden,
    BreakOutsideOfLoop,
    ContinueOutsideOfLoop,
    ThirtyTwoBitUnsupported,
    ImportFailed(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IdentifierNotFound(id) => write!(f, "identifier {id} not found"),
            Error::TypeNotFound(td) => write!(f, "type {td} not found"),
            Error::TypeNotRefcounted(td) => {
                if let Some(td) = td {
                    write!(f, "type {td} cannot be dynamically memory managed")
                } else {
                    write!(f, "this type cannot be dynamically memory managed")
                }
            }
            Error::UnexpectedType(opt) => {
                if let Some(opt) = opt {
                    write!(f, "type mismatch in expression: expected {opt}")
                } else {
                    write!(f, "type mismatch in expression")
                }
            }
            Error::ArgCountMismatch(expected, actual) => {
                write!(f, "{expected} args expected, {actual} actual")
            }
            Error::OverloadSetEmptyArgc(name, argc) => {
                write!(f, "no overload of {name} takes {argc} arguments")
            }
            Error::OverloadSetEmptyArgv(name) => {
                write!(f, "no overload of {name} accepts the arguments provided")
            }
            Error::OverloadSetAmbiguous(name) => {
                write!(
                    f,
                    "multiple overloads of {name} can accept the arguments provided"
                )
            }
            Error::InvalidExpression => write!(f, "invalid expression"),
            Error::InvalidCast => write!(f, "invalid type cast"),
            Error::DotAccessInvalid => write!(f, "invalid dot access usage"),
            Error::FieldNotFound(name) => write!(f, "field {name} not found"),
            Error::UnexpectedState(s) => write!(f, "invalid state, expected {s}"),
            Error::InternalError(err) => write!(f, "{err}"),
            Error::ParseError(err) => write!(f, "parse error, expected {err}"),
            Error::RecursiveTypeForbidden(field) => {
                write!(f, "field {field} would cause this type to be recursive")
            }
            Error::ReadOnlyIdentifier(id) => write!(f, "{id} is read-only"),
            Error::ReservedIdentifier(id) => write!(f, "identifier {id} is reserved"),
            Error::WarningAsError(warn) => write!(f, "warning treated as error: {warn}"),
            Error::InvalidTypeSpecifier(expected, actual) => write!(
                f,
                "type specifier {expected} doesn't match actual type of value {actual}"
            ),
            Error::DuplicateArgumentName(name) => {
                write!(f, "argument {name} already defined for this function")
            }
            Error::UnresolvedVariableDeclaration => {
                write!(f, "this declaration cannot be resolved to a type")
            }
            Error::LetMustBeInitialized => {
                write!(f, "delayed writing to a let value is not implemented")
            }
            Error::RefTypeInValTypeForbidden => {
                write!(f, "ref type field of val type is not implemented")
            }
            Error::DuplicatedStructMember(name) => {
                write!(f, "member {name} has already been defined for this type")
            }
            Error::InitDisallowedInValueTypes | Error::DeallocDisallowedInValueTypes => {
                write!(f, "this declaration is only permitted for reference types")
            }
            Error::InitMustBeUsed => {
                write!(
                    f,
                    "this type provides init, which must be called when allocating"
                )
            }
            Error::BreakOutsideOfLoop | Error::ContinueOutsideOfLoop => {
                write!(f, "this statement cannot be used outside of a loop")
            }
            Error::ThirtyTwoBitUnsupported => {
                write!(f, "C± does not support compilation for 32-bit targets")
            }
            Error::ImportFailed(name) => {
                write!(f, "import of declaration {name} failed")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum CompilerDiagnostic {
    Error(CompilerError),
    Warning(CompilerWarning),
}

#[derive(Clone, Debug)]
pub struct CompilerError {
    pub loc: TokenSpan,
    pub err: Error,
}

impl CompilerError {
    pub fn new(loc: TokenSpan, err: Error) -> Self {
        Self { loc, err }
    }
    pub fn unbound(err: Error) -> Self {
        Self {
            loc: TokenSpan::origin(),
            err,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Warning {
    MutabilityArgInExternFunction,
    MutableValueNeverWrittenTo(String),
    LocalValueNeverAccessed(String),
    ExportInLocalDeclUnused,
    ExportImplIgnored,
    CannotInstrumentJitRefcount,
}

impl Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::MutabilityArgInExternFunction => {
                write!(f, "var/let specification in extern function has no purpose")
            }
            Warning::MutableValueNeverWrittenTo(name) => {
                write!(f, "variable {name} declared mutable but never written to")
            }
            Warning::LocalValueNeverAccessed(name) => {
                write!(f, "variable {name} was declared but never used")
            }
            Warning::ExportInLocalDeclUnused => {
                write!(f, "export is ignored outside of top-level declarations")
            }
            Warning::ExportImplIgnored => {
                write!(
                    f,
                    "this type is not exported; export of its impls is ignored"
                )
            }
            Warning::CannotInstrumentJitRefcount => {
                write!(
                    f,
                    "instrumenting refcounting API not supported when in JIT mode"
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompilerWarning {
    pub loc: TokenSpan,
    pub warn: Warning,
}

impl CompilerWarning {
    pub fn new(loc: TokenSpan, warn: Warning) -> Self {
        Self { loc, warn }
    }
    pub fn unbound(warn: Warning) -> Self {
        Self {
            loc: TokenSpan::origin(),
            warn,
        }
    }
}
