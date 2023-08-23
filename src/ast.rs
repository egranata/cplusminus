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

use serde::{Deserialize, Serialize};

use crate::codegen::structure::MemoryStrategy;

#[derive(Copy, Clone, Debug)]
pub struct TokenSpan {
    pub start: usize,
    pub end: usize,
}

impl TokenSpan {
    pub fn origin() -> Self {
        Self { start: 0, end: 0 }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TokenLocation {
    pub line: usize,
    pub column: usize,
}

// defined not inline within the TypeDescriptor because it
// makes the resulting BOM easier to read
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FunctionTypeDescriptor {
    pub args: Vec<TypeDescriptor>,
    pub ret: Option<Box<TypeDescriptor>>,
    pub vararg: bool,
}

impl FunctionTypeDescriptor {
    pub fn new(args: Vec<TypeDescriptor>, ret: Option<Box<TypeDescriptor>>, vararg: bool) -> Self {
        Self { args, ret, vararg }
    }
}

// it's not ideal to serialize an AST entry directly
// but TypeDescriptor is pretty much good enough that I'd just
// end up writing a copy of it
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum TypeDescriptor {
    Name(String),
    Pointer(Box<TypeDescriptor>),
    Array(Box<TypeDescriptor>, usize),
    Function(FunctionTypeDescriptor),
    Tuple(Vec<TypeDescriptor>),
}

fn join_commad_list<T: Display>(l: &[T]) -> String {
    let mut out = String::from("");
    let mut first = true;
    for item in l {
        if first {
            out = format!("{item}");
            first = false;
        } else {
            out = format!("{out},{item}");
        }
    }

    out
}

impl Display for TypeDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeDescriptor::Name(name) => write!(f, "{name}"),
            TypeDescriptor::Pointer(pte) => write!(f, "*{pte}"),
            TypeDescriptor::Array(ty, sz) => write!(f, "[{sz}]{ty}"),
            TypeDescriptor::Function(ftd) => {
                let s = join_commad_list(&ftd.args);
                write!(
                    f,
                    "{}fn({s}){}",
                    if ftd.vararg { "vararg " } else { "" },
                    if let Some(ret) = &ftd.ret {
                        format!(" ret {ret}")
                    } else {
                        String::new()
                    }
                )
            }
            TypeDescriptor::Tuple(at) => {
                let s = join_commad_list(at);
                write!(f, "tuple({s})")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDecl {
    pub loc: TokenSpan,
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
    pub loc: TokenSpan,
    pub imp: FunctionDefinition,
}

#[derive(Clone, Debug)]
pub struct InitDecl {
    pub loc: TokenSpan,
    pub args: Vec<FunctionArgument>,
    pub body: Statement,
}

#[derive(Clone, Debug)]
pub struct DeallocDecl {
    pub loc: TokenSpan,
    pub body: Statement,
}

#[derive(Clone, Debug)]
pub enum StructEntryDecl {
    Field(FieldDecl),
    Init(InitDecl),
    Dealloc(DeallocDecl),
}

#[derive(Clone, Debug)]
pub struct RawStructDecl {
    pub loc: TokenSpan,
    pub name: String,
    pub ms: MemoryStrategy,
    pub entries: Vec<StructEntryDecl>,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct ProperStructDecl {
    pub loc: TokenSpan,
    pub name: String,
    pub ms: MemoryStrategy,
    pub fields: Vec<FieldDecl>,
    pub init: Option<InitDecl>,
    pub dealloc: Option<DeallocDecl>,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub loc: TokenSpan,
    pub of: TypeDescriptor,
    pub methods: Vec<MethodDecl>,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct FunctionArgument {
    pub loc: TokenSpan,
    pub name: String,
    pub ty: TypeDescriptor,
    pub rw: bool,
    pub explicit_rw: bool,
}

#[derive(Clone, Debug)]
pub struct IfCondition {
    pub loc: TokenSpan,
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
    pub loc: TokenSpan,
    pub name: String,
    pub args: Vec<FunctionArgument>,
    pub ty: TypeDescriptor,
}

#[derive(Clone, Debug)]
pub struct ExternFunction {
    pub loc: TokenSpan,
    pub decl: FunctionDecl,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct FunctionDefinition {
    pub decl: FunctionDecl,
    pub body: Statement,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub enum Lvalue {
    Identifier(String),
    Dotted(Box<Lvalue>, String),
    Indexed(Box<Lvalue>, Box<Expression>),
    Increment(Box<Lvalue>),
    Decrement(Box<Lvalue>),
}

impl Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lvalue::Identifier(id) => write!(f, "{id}"),
            Lvalue::Dotted(parent, id) => write!(f, "{parent}.{id}"),
            Lvalue::Indexed(parent, _) => write!(f, "{parent}[todo]"),
            Lvalue::Increment(parent) => write!(f, "inc {parent}"),
            Lvalue::Decrement(parent) => write!(f, "dec {parent}"),
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
    ByFieldList(Vec<FieldInitializer>),
    ByInit(Vec<Expression>),
}

#[derive(Clone, Debug, Copy)]
pub enum Number {
    Integer(i64),
    FloatingPoint(f64),
}

#[derive(Clone, Debug)]
pub enum TypeProperty {
    Size,
    Alignment,
}

#[derive(Clone, Debug)]
pub enum Expr {
    ConstantNumber(Number),
    ConstString(String),
    Addition(Box<Expression>, Box<Expression>),
    Subtraction(Box<Expression>, Box<Expression>),
    UnaryMinus(Box<Expression>),
    UnaryNot(Box<Expression>),
    Multiplication(Box<Expression>, Box<Expression>),
    Division(Box<Expression>, Box<Expression>),
    Modulo(Box<Expression>, Box<Expression>),
    ShiftLeft(Box<Expression>, Box<Expression>),
    ShiftRight(Box<Expression>, Box<Expression>),
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
    Alloc(TypeDescriptor, Option<AllocInitializer>),
    Incref(Box<Expression>),
    Getref(Box<Expression>),
    Rvalue(Lvalue),
    Cast(Box<Expression>, TypeDescriptor),
    Array(Vec<Expression>),
    PropertyofVar(Box<Expression>, TypeProperty),
    PropertyofType(TypeDescriptor, TypeProperty),
    Deref(Box<Expression>),
    Tuple(Vec<Expression>),
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
        if let Expr::ConstantNumber(Number::Integer(n)) = &self {
            Some(*n)
        } else {
            None
        }
    }

    pub fn as_float_const(&self) -> Option<f64> {
        if let Expr::ConstantNumber(Number::FloatingPoint(n)) = &self {
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
pub struct GlobalVarDecl {
    pub loc: TokenSpan,
    pub decl: VarDecl,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct WhileStmt {
    pub cond: Box<Expression>,
    pub body: Box<Statement>,
    pub els: Option<Box<Statement>>,
}

#[derive(Clone, Debug)]
pub struct DoWhileStmt {
    pub body: Box<Statement>,
    pub cond: Box<Expression>,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    VarDecl(VarDecl),
    Return(Option<Expression>),
    Assignment(Lvalue, Box<Expression>),
    If(IfStatement),
    Block(Vec<Statement>),
    Expression(Box<Expression>),
    While(WhileStmt),
    DoWhile(DoWhileStmt),
    Decref(Box<Expression>),
    Assert(Box<Expression>),
    TypeAlias(TypeAliasDecl),
    Function(Box<FunctionDefinition>),
    Break,
    Continue,
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub loc: TokenSpan,
    pub payload: Expr,
}

impl Expression {
    pub fn as_identifier(&self) -> Option<&str> {
        self.payload.as_identifier()
    }

    pub fn identifier(loc: TokenSpan, i: &str) -> Expression {
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
    pub loc: TokenSpan,
    pub name: String,
    pub ty: TypeDescriptor,
    pub export: bool,
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub loc: TokenSpan,
    pub payload: Stmt,
}

#[derive(Clone, Debug)]
pub struct ImportDecl {
    pub loc: TokenSpan,
    pub path: String,
}

#[derive(Clone, Debug)]
pub enum TopLevelDecl {
    Function(FunctionDefinition),
    Extern(ExternFunction),
    Structure(RawStructDecl),
    Alias(TypeAliasDecl),
    Implementation(ImplDecl),
    Variable(GlobalVarDecl),
    Import(ImportDecl),
}

impl TopLevelDecl {
    pub fn names(&self) -> Vec<String> {
        match self {
            TopLevelDecl::Function(f) => vec![f.decl.name.clone()],
            TopLevelDecl::Extern(e) => vec![e.decl.name.clone()],
            TopLevelDecl::Structure(s) => vec![s.name.clone()],
            TopLevelDecl::Alias(a) => vec![a.name.clone()],
            TopLevelDecl::Variable(v) => vec![v.decl.name.clone()],
            TopLevelDecl::Implementation(..) | TopLevelDecl::Import(..) => vec![],
        }
    }
}

#[derive(Clone, Debug)]
pub struct TopLevelDeclaration {
    pub loc: TokenSpan,
    pub payload: TopLevelDecl,
}

impl TopLevelDeclaration {
    pub fn names(&self) -> Vec<String> {
        self.payload.names()
    }

    pub fn function(l: TokenSpan, f: FunctionDefinition) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Function(f),
        }
    }

    pub fn extern_function(l: TokenSpan, f: ExternFunction) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Extern(f),
        }
    }

    pub fn structure(l: TokenSpan, s: RawStructDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Structure(s),
        }
    }

    pub fn typealias(l: TokenSpan, a: TypeAliasDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Alias(a),
        }
    }

    pub fn implementation(l: TokenSpan, i: ImplDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Implementation(i),
        }
    }

    pub fn variable(l: TokenSpan, v: GlobalVarDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Variable(v),
        }
    }

    pub fn import(l: TokenSpan, i: ImportDecl) -> Self {
        Self {
            loc: l,
            payload: TopLevelDecl::Import(i),
        }
    }
}
