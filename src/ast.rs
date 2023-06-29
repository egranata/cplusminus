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

use crate::codegen::structure::MemoryStrategy;

#[derive(Copy, Clone, Debug)]
pub struct Location {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug)]
pub enum TypeDescriptor {
    Name(String),
    Pointer(Box<TypeDescriptor>),
    Array(Box<TypeDescriptor>, usize),
    Function(Vec<TypeDescriptor>, Box<TypeDescriptor>, bool),
}

impl Display for TypeDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeDescriptor::Name(name) => write!(f, "{name}"),
            TypeDescriptor::Pointer(pte) => write!(f, "*{pte}"),
            TypeDescriptor::Array(ty, sz) => write!(f, "[{sz}]{ty}"),
            TypeDescriptor::Function(..) => write!(f, "func todo"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDecl {
    pub loc: Location,
    pub name: String,
    pub ty: TypeDescriptor,
}

#[derive(Clone, Debug)]
pub struct MethodCall {
    pub this: Box<Expression>,
    pub name: String,
    pub args: Vec<Expression>,
}

#[derive(Clone, Debug)]
pub struct MethodDecl {
    pub loc: Location,
    pub imp: FunctionDefinition,
}

#[derive(Clone, Debug)]
pub struct StructDecl {
    pub loc: Location,
    pub name: String,
    pub ms: MemoryStrategy,
    pub fields: Vec<FieldDecl>,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub loc: Location,
    pub name: String,
    pub methods: Vec<MethodDecl>,
}

#[derive(Clone, Debug)]
pub struct FunctionArgument {
    pub loc: Location,
    pub name: String,
    pub ty: TypeDescriptor,
    pub rw: bool,
    pub explicit_rw: bool,
}

#[derive(Clone, Debug)]
pub struct IfCondition {
    pub loc: Location,
    pub cond: Box<Expression>,
    pub body: Box<Statement>,
}

#[derive(Clone, Debug)]
pub struct IfStatement {
    pub base: IfCondition,
    pub alts: Vec<IfCondition>,
    pub othw: Option<Box<Statement>>,
}

#[derive(Clone, Debug)]
pub struct FunctionDecl {
    pub loc: Location,
    pub name: String,
    pub args: Vec<FunctionArgument>,
    pub vararg: bool,
    pub ty: TypeDescriptor,
}

#[derive(Clone, Debug)]
pub struct FunctionDefinition {
    pub decl: FunctionDecl,
    pub body: Statement,
}

#[derive(Clone, Debug)]
pub enum Lvalue {
    Identifier(String),
    Dotted(Box<Lvalue>, String),
    Indexed(Box<Lvalue>, Box<Expression>),
}

impl Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lvalue::Identifier(id) => write!(f, "{id}"),
            Lvalue::Dotted(parent, id) => write!(f, "{parent}.{id}"),
            Lvalue::Indexed(parent, _) => write!(f, "{parent}[todo]"),
        }
    }
}

impl From<&Lvalue> for String {
    fn from(value: &Lvalue) -> Self {
        format!("{value}")
    }
}
impl From<Lvalue> for String {
    fn from(value: Lvalue) -> Self {
        format!("{value}")
    }
}

#[derive(Clone, Debug)]
pub struct FieldInitializer {
    pub field: String,
    pub value: Box<Expression>,
}

#[derive(Clone, Debug)]
pub enum AllocInitializer {
    None,
    ValueType(Vec<FieldInitializer>),
    // ReferenceType(...),
}

#[derive(Clone, Debug)]
pub enum Expr {
    ConstInt(i64),
    ConstString(String),
    Addition(Box<Expression>, Box<Expression>),
    Subtraction(Box<Expression>, Box<Expression>),
    UnaryMinus(Box<Expression>),
    UnaryNot(Box<Expression>),
    Multiplication(Box<Expression>, Box<Expression>),
    Division(Box<Expression>, Box<Expression>),
    Modulo(Box<Expression>, Box<Expression>),
    Equality(Box<Expression>, Box<Expression>),
    NotEqual(Box<Expression>, Box<Expression>),
    GreaterThan(Box<Expression>, Box<Expression>),
    LessThan(Box<Expression>, Box<Expression>),
    GreaterEqual(Box<Expression>, Box<Expression>),
    LessEqual(Box<Expression>, Box<Expression>),
    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
    XOr(Box<Expression>, Box<Expression>),
    FunctionCall(String, Vec<Expression>),
    MethodCall(MethodCall),
    PointerFunctionCall(Box<Expression>, Vec<Expression>),
    Alloc(TypeDescriptor, AllocInitializer),
    Incref(Box<Expression>),
    Getref(Box<Expression>),
    Rvalue(Lvalue),
    Cast(Box<Expression>, TypeDescriptor),
    Array(Vec<Expression>),
    SizeofVar(Box<Expression>),
    SizeofTy(TypeDescriptor),
    Deref(Box<Expression>),
    AddressOf(Lvalue),
}

impl Expr {
    pub fn as_identifier(&self) -> Option<&str> {
        if let Expr::Rvalue(Lvalue::Identifier(id)) = &self {
            Some(id)
        } else {
            None
        }
    }

    pub fn as_int_const(&self) -> Option<i64> {
        if let Expr::ConstInt(n) = &self {
            Some(*n)
        } else {
            None
        }
    }

    pub fn identifier(i: &str) -> Expr {
        Expr::Rvalue(Lvalue::Identifier(i.to_string()))
    }
}

#[derive(Clone, Debug)]
pub struct VarDecl {
    pub name: String,
    pub ty: Option<TypeDescriptor>,
    pub val: Option<Expression>,
    pub rw: bool,
}

#[derive(Clone, Debug)]
pub struct WhileStmt {
    pub cond: Box<Expression>,
    pub body: Box<Statement>,
    pub els: Option<Box<Statement>>,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    VarDecl(VarDecl),
    Return(Box<Expression>),
    Assignment(Lvalue, Box<Expression>),
    If(IfStatement),
    Block(Vec<Statement>),
    Expression(Box<Expression>),
    While(WhileStmt),
    Decref(Box<Expression>),
    Assert(Box<Expression>),
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub loc: Location,
    pub payload: Expr,
}

impl Expression {
    pub fn as_identifier(&self) -> Option<&str> {
        self.payload.as_identifier()
    }

    pub fn identifier(loc: Location, i: &str) -> Expression {
        Self {
            loc,
            payload: Expr::identifier(i),
        }
    }

    pub fn as_int_const(&self) -> Option<i64> {
        self.payload.as_int_const()
    }
}

#[derive(Clone, Debug)]
pub struct TypeAliasDecl {
    pub loc: Location,
    pub name: String,
    pub ty: TypeDescriptor,
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub loc: Location,
    pub payload: Stmt,
}

#[derive(Clone, Debug)]
pub enum TopLevelDecl {
    Function(FunctionDefinition),
    ExternFunction(FunctionDecl),
    Structure(StructDecl),
    Alias(TypeAliasDecl),
    Implementation(ImplDecl),
}

#[derive(Clone, Debug)]
pub struct TopLevelDeclaration {
    pub loc: Location,
    pub payload: TopLevelDecl,
}

impl TopLevelDeclaration {
    pub fn function(l: Location, f: FunctionDefinition) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Function(f),
        }
    }

    pub fn extern_function(l: Location, f: FunctionDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::ExternFunction(f),
        }
    }

    pub fn structure(l: Location, s: StructDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Structure(s),
        }
    }

    pub fn typealias(l: Location, a: TypeAliasDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Alias(a),
        }
    }

    pub fn implementation(l: Location, i: ImplDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Implementation(i),
        }
    }
}
