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

use crate::ast::{Location, TypeDescriptor};

#[derive(Clone, Debug)]
pub enum Error {
    IdentifierNotFound(String),
    TypeNotFound(TypeDescriptor),
    TypeNotRefcounted(Option<TypeDescriptor>),
    UnexpectedType(Option<String>),
    ArgCountMismatch(usize, usize),
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
    InitMustBeUsed,
    WarningAsError(Warning),
    InvalidTypeSpecifier(TypeDescriptor, TypeDescriptor),
    DuplicateArgumentName(String),
    UnresolvedVariableDeclaration,
    LetMustBeInitialized,
    RefTypeInValTypeForbidden,
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
            Error::InitDisallowedInValueTypes => {
                write!(f, "init is only permitted for reference types")
            }
            Error::InitMustBeUsed => {
                write!(
                    f,
                    "this type provides init, which must be called when allocating"
                )
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
    pub loc: Location,
    pub err: Error,
}

impl CompilerError {
    pub fn new(loc: Location, err: Error) -> Self {
        Self { loc, err }
    }
}

#[derive(Clone, Debug)]
pub enum Warning {
    MutabilityArgInExternFunction,
    MutableValueNeverWrittenTo(String),
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
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompilerWarning {
    pub loc: Location,
    pub warn: Warning,
}

impl CompilerWarning {
    pub fn new(loc: Location, warn: Warning) -> Self {
        Self { loc, warn }
    }
}
