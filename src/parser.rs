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

use crate::ast::*;
use peg;

fn escape_string(x: &str) -> String {
    x.replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
}

fn is_syntactically_magic(x: char) -> bool {
    x == '[' || x == '*'
}

fn is_valid_ident_first(x: char) -> bool {
    !is_syntactically_magic(x)
        && (unicode_ident::is_xid_start(x) || x == '_' || x == '$' || unic_emoji_char::is_emoji(x))
}

fn is_valid_ident_next(x: char) -> bool {
    !is_syntactically_magic(x)
        && (unicode_ident::is_xid_continue(x)
            || x == '_'
            || x == '$'
            || unic_emoji_char::is_emoji(x))
}

peg::parser! {
    pub grammar cpm() for str {
        rule decimal_integer() -> i64
        = n:$(['0'..='9']+) {? n.parse().or(Err("u32")) };

        rule hex_integer() -> i64 =
        "x" n:$(['0'..='9' | 'A'..='F' | 'a'..='f']+) { i64::from_str_radix(n, 16).unwrap() }

        rule octal_integer() -> i64 =
        "o" n:$(['0'..='7']+) { i64::from_str_radix(n, 8).unwrap() }

        rule binary_integer() -> i64 =
        "b" n:$(['0'..='1']+) { i64::from_str_radix(n, 2).unwrap() }

        rule number() -> i64 =
        (decimal_integer() / hex_integer() / octal_integer() / binary_integer()) / expected!("number");

        rule strlit() -> String
        = "\"" s:$((!"\"" [_])*) "\"" { escape_string(s) }

        rule ident() -> String =
        s:$([c if is_valid_ident_first(c)] [c if is_valid_ident_next(c)]*) { s.to_owned() }

        rule typename_ident() -> TypeDescriptor
        = i:ident() { TypeDescriptor::Name(i.clone()) }
        rule typename_ptr() -> TypeDescriptor =
        "*" t:typename() { TypeDescriptor::Pointer(Box::new(t)) }
        rule typename_arr() -> TypeDescriptor =
        "[" n:number() "]" t:typename() { TypeDescriptor::Array(Box::new(t),n as usize) }
        rule typename_func() -> TypeDescriptor =
        "fn" _ "(" _ at:typename()**"," _ ")" _ "ret" _ rt:typename() { TypeDescriptor::Function(at, Box::new(rt), false) }

        rule typename() -> TypeDescriptor =
        _ t:(typename_func() / typename_ident() / typename_ptr() / typename_arr()) _ {t} / expected!("name of a type")


        rule comment_start() -> ()
        = "(*"

        rule comment_end() -> ()
            = "*)" [' ']* "\n"

        rule comment_content() -> ()
            = comment()
            / (!comment_start() !comment_end() [_])

        rule comment() -> ()
            = (comment_start() comment_content()* comment_end())

        rule _() = (comment() / [' ' | '\t' | '\r' | '\n'])*

        rule __() = [' ' | '\t' | '\r' | '\n']+

        rule array_expr() -> Expr =
        "[" _ es:top_level_expr()**"," _ "]" { Expr::Array(es) }

        rule value_type_alloc_entry() -> FieldInitializer =
        _ i:ident() _ ":" _ e:top_level_expr() _ {
            FieldInitializer{ field: i, value: Box::new(e) }
        }

        rule value_type_alloc_entries() -> AllocInitializer =
        _ "{" _ p:value_type_alloc_entry()**"," _ "}" { AllocInitializer::ByFieldList(p) }

        rule ref_type_alloc_entries() -> AllocInitializer =
        _ "(" _ p:func_call_args() _ ")" { AllocInitializer::ByInit(p) }

        rule alloc_init_expr() -> AllocInitializer =
        value_type_alloc_entries() / ref_type_alloc_entries();

        pub rule expr() -> Expression = precedence!{
            start:position!() node:@ end:position!() { Expression { loc:Location{start,end}, payload:node} }

            ae:array_expr() { ae }
            --
            x:(@) __() "as" __() ty:typename() { Expr::Cast(Box::new(x), ty) }
            x:(@) _ "==" _ y:@ { Expr::Equality(Box::new(x), Box::new(y)) }
            x:(@) _ "!=" _ y:@ { Expr::NotEqual(Box::new(x), Box::new(y)) }
            x:(@) _ ">" _ y:@ { Expr::GreaterThan(Box::new(x), Box::new(y)) }
            x:(@) _ "<" _ y:@ { Expr::LessThan(Box::new(x), Box::new(y)) }
            x:(@) _ ">=" _ y:@ { Expr::GreaterEqual(Box::new(x), Box::new(y)) }
            x:(@) _ "<=" _ y:@ { Expr::LessEqual(Box::new(x), Box::new(y)) }
            --
            "alloc" __() ty:typename() _ init:alloc_init_expr()? {
                Expr::Alloc(ty, init)
            }
            "incref" __() e:expr() _ { Expr::Incref(Box::new(e)) }
            "getref" __() e:expr() _ { Expr::Getref(Box::new(e)) }
            "sizeof" __() "expr" __() e:expr() _ { Expr::SizeofVar(Box::new(e)) }
            "sizeof" __() "type" __() ty:typename() _ { Expr::SizeofTy(ty) }
            --
            x:(@) _ "<<" _ y:@ { Expr::ShiftLeft(Box::new(x), Box::new(y)) }
            x:(@) _ ">>" _ y:@ { Expr::ShiftRight(Box::new(x), Box::new(y)) }
            --
            x:(@) _ "+" _ y:@ { Expr::Addition(Box::new(x), Box::new(y)) }
            x:(@) _ "||" _ y:@ { Expr::Or(Box::new(x), Box::new(y)) }
            x:(@) _ "^^" _ y:@ { Expr::XOr(Box::new(x), Box::new(y)) }
            x:(@) _ "-" _ y:@ { Expr::Subtraction(Box::new(x), Box::new(y)) }
                    "-" _ y:@ { Expr::UnaryMinus(Box::new(y)) }
                    "!" _ y:@ { Expr::UnaryNot(Box::new(y)) }
            --
            x:(@) _ "*" _ y:@ { Expr::Multiplication(Box::new(x), Box::new(y)) }
            x:(@) _ "&&" _ y:@ { Expr::And(Box::new(x), Box::new(y)) }
            x:(@) _ "/" _ y:@ { Expr::Division(Box::new(x), Box::new(y)) }
            x:(@) _ "%" _ y:@ { Expr::Modulo(Box::new(x), Box::new(y)) }
            --
            this:(@) "->" name:ident() "(" args:func_call_args() ")" {
                let mc = MethodCall{ this:Box::new(this), name, args };
                Expr::MethodCall(mc)
            }
            i:ident() _ "(" a:func_call_args() ")" { Expr::FunctionCall(i,a) }
            "&" lv:lvalue() _ { Expr::AddressOf(lv) }
            "*" e:expr() { Expr::Deref(Box::new(e)) }
            --
            "inc" __() lv:lvalue() { Expr::Increment(lv) }
            "dec" __() lv:lvalue() { Expr::Decrement(lv) }
            --
            n:number() { Expr::ConstInt(n) }
            s:strlit() { Expr::ConstString(s) }
            lv:lvalue() { Expr::Rvalue(lv) }
            "(" _ e:expr() _ ")" { e.payload }
        }

        rule top_level_expr() -> Expression =
        _ c:expr() _ { c }

        rule var_decl_rw_ro() -> bool =
        "var" { true } /
        "let" { false }

        rule type_decl() -> TypeDescriptor =
        _ ":" _ ty:typename() _ { ty }

        rule eq_assignment() -> Expression =
        _ "=" _ e:top_level_expr() _ { e }

        rule var_decl_body() -> VarDecl =
        rw:var_decl_rw_ro() __() i:ident() _ ty:type_decl()? _ e:eq_assignment()? {
            VarDecl{name:i,ty,val:e,rw}
        }

        rule var_decl_stmt() -> Statement =
        start:position!() vd:var_decl_body() _ end:position!() {
            Statement { loc:Location{start,end}, payload:Stmt::VarDecl(vd) }
        }

        rule ret_payload() -> Expression =
        __() e:top_level_expr() { e }

        rule ret() -> Statement =
        start:position!() "return" e:ret_payload()? end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Return(e) } }

        #[cache_left_rec]
        rule lvalue() -> Lvalue =
        b:lvalue() "[" e:top_level_expr() "]" { Lvalue::Indexed(Box::new(b), Box::new(e)) } /
        b:lvalue() "." i:ident() { Lvalue::Dotted(Box::new(b), i) } /
        i:ident() { Lvalue::Identifier(i) }

        rule assignment() -> Statement =
        start:position!() lv:lvalue() _ "=" _ e:top_level_expr() end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Assignment(lv,Box::new(e)) } }

        rule ifcond() -> IfCondition =
        start:position!() "(" _ cond:top_level_expr() _ ")" _ body:block() end:position!() { IfCondition{loc:Location{start,end},cond:Box::new(cond),body:Box::new(body)} }

        rule ifcheck() -> IfCondition =
        "if" _ cond:ifcond() _ { cond }

        rule elsifcheck() -> IfCondition =
        "elsif" _ cond:ifcond() _ { cond }

        rule elscheck() -> Box<Statement> =
        "else" _ blk:block() { Box::new(blk) }

        rule field_decl() -> StructEntryDecl =
        start:position!() _ n:ident() _ ty:type_decl() _ end:position!() {
            let field = FieldDecl { loc:Location{start,end}, name:n, ty };
            StructEntryDecl::Field(field)
        }

        rule init_decl() -> StructEntryDecl =
        _ start:position!() _ "init" _ "(" _ args:func_arg()**"," _ ")" _ body:block() end:position!() _ {
            let init = InitDecl { loc:Location{start, end}, args, body };
            StructEntryDecl::Init(init)
        }

        rule dealloc_decl() -> StructEntryDecl =
        _ start:position!() _ "dealloc" _ body:block() end:position!() _ {
            let dealloc = DeallocDecl { loc:Location{start, end}, body };
            StructEntryDecl::Dealloc(dealloc)
        }

        rule struct_entry() -> StructEntryDecl = field_decl() / init_decl() / dealloc_decl();

        rule ref_val_decl() -> bool =
        _ s:$("ref" / "val") __() { s == "ref" }

        rule struct_decl() -> TopLevelDeclaration =
        _ start:position!() rd:ref_val_decl()? "type" __() n:ident() _ "{" _ f:(struct_entry()**",") _ "}" end:position!() _ {
            let ms = if rd.unwrap_or(true) { crate::codegen::structure::MemoryStrategy::ByReference } else { crate::codegen::structure::MemoryStrategy::ByValue };
            let sd = RawStructDecl { loc:Location{start,end}, name:n, ms, entries:f };
            TopLevelDeclaration::structure(sd.loc, sd)
        }

        rule ifstmt() -> Statement =
        start:position!() a:ifcheck() _ b:elsifcheck()* _ c:elscheck()? end:position!() { Statement { loc:Location{start,end}, payload: Stmt::If(IfStatement{base:a,alts:b,othw:c}) } }

        rule expr_stmt() -> Statement =
        start:position!() e:top_level_expr() end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Expression(Box::new(e)) } }

        rule whilestmt() -> Statement =
        start:position!() "while" _ "(" c:top_level_expr() _ ")" _ blk:block() _ els:elscheck()? end:position!()  {
            let wh = WhileStmt {
                cond: Box::new(c),
                body: Box::new(blk),
                els,
            };
            Statement { loc:Location{start,end}, payload:Stmt::While(wh) }
        }

        rule decrefstmt() -> Statement =
        start:position!() "decref" __() c:top_level_expr() _ end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Decref(Box::new(c)) } }

        rule assertstmt() -> Statement =
        start:position!() "assert" __() c:top_level_expr() _ end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Assert(Box::new(c)) } }

        rule typealiasstmt() -> Statement =
        decl:typealias() {
            Statement { loc:decl.loc, payload:Stmt::TypeAlias(decl) }
        }

        rule top_level_statement() -> Statement =
        _ v:(var_decl_stmt() / assignment() / typealiasstmt() / function_def_stmt() / ifstmt() / whilestmt() / ret() / decrefstmt() / assertstmt() / block() / expr_stmt()) _ ";" {v}

        rule block() -> Statement =
        start:position!() "{" _ s:top_level_statement()* _ "}" end:position!() { Statement { loc:Location{start,end}, payload:Stmt::Block(s) } }

        rule func_arg() -> FunctionArgument =
        _ start:position!() rw:var_decl_rw_ro()? _ name:ident() _ ty:type_decl() end:position!() _ { FunctionArgument{loc:Location{start,end}, name,ty,rw:rw.unwrap_or(false), explicit_rw:rw.is_some()} }

        rule function_ret() -> TypeDescriptor =
        _ "ret" _ ty:typename() _ { ty }

        rule extern_function() -> TopLevelDeclaration =
        _ start:position!() "extern" __() v:("vararg")? "func" __() name:ident() "(" _ args:func_arg()**"," _ ")" _ ty:function_ret()? _ ";" _ end:position!() _ {
            let decl = FunctionDecl { loc:Location{start,end}, name,args,vararg:v.is_some(),ty };
            TopLevelDeclaration::extern_function(decl.loc, decl)
        }

        rule inner_function_def() -> FunctionDefinition =
        _ start:position!() "func" __() name:ident() "(" _ args:func_arg()**"," _ ")" _ ty:function_ret()? decl_end:position!() _ body:block() end:position!() _ {
            let decl = FunctionDecl { loc:Location{start,end:decl_end}, name,args,vararg:false,ty };
            FunctionDefinition { decl,body }
        }

        rule function_def_stmt() -> Statement =
        decl:inner_function_def() {
            Statement { loc:decl.decl.loc, payload:Stmt::Function(Box::new(decl)) }
        }

        rule method_def() -> MethodDecl = fd:inner_function_def() {
            MethodDecl { loc:fd.decl.loc, imp:fd }
        }

        rule function() -> TopLevelDeclaration = def:inner_function_def() {
            TopLevelDeclaration::function(def.decl.loc, def)
        }

        rule typealias() -> TypeAliasDecl =
        _ start:position!() "type" __() name:ident() _ "=" _ ty:typename() _ end:position!() _ {
            TypeAliasDecl {loc:Location{start,end}, name, ty}
        }

        rule typealias_tld() -> TopLevelDeclaration =
        decl:typealias() _ ";" _ {
            TopLevelDeclaration::typealias(decl.loc,decl)
        }

        rule impl_def() -> ImplDecl =
        _ start:position!() "impl" __() name:ident() _ "{" _ methods:method_def()* _ "}" _ end:position!() _ {
            ImplDecl { loc:Location{start,end}, name, methods }
        }

        rule implementation() -> TopLevelDeclaration = id:impl_def() {
            TopLevelDeclaration::implementation(id.loc, id)
        }

        rule var_decl_toplevel() -> TopLevelDeclaration =
        _ start:position!() vd:var_decl_body() _ ";" _ end:position!() {
            let loc = Location{start,end};
            TopLevelDeclaration::variable(loc, vd)
        }

        rule func_call_args() -> Vec<Expression> =
        top_level_expr()**","

        pub rule source_file() -> Vec<TopLevelDeclaration> =
        (struct_decl() / function() / extern_function() / typealias_tld() / implementation() / var_decl_toplevel())* / expected!("function or structure")
    }
}
