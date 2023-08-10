use crate::{Expr, ExprId, Function, Body, Name, Stmt, TypeRef, TypeRefId};
use la_arena::Arena;
use std::fmt::Write;

pub fn print_function(function: &Function, body: &Body) -> String {
    let mut s = String::new();
    print_function_(&mut s, function, body);
    s
}

fn print_function_(s: &mut String, function: &Function, body: &Body) {
    s.push_str("fn");
    s.push(' ');
    print_name(s, &function.name);
    s.push('(');
    for (i, ty) in function.param_tys.iter().copied().enumerate() {
        if i > 0 {
            s.push(',');
            s.push(' ');
        }
        print_type_ref(s, function, ty);
    }
    s.push(')');
    s.push(' ');
    print_type_ref(s, function, function.return_ty);
    s.push(' ');
    print_expr(s, &body.exprs, body.expr, 0);
}

fn print_type_ref(s: &mut String, function: &Function, ty: TypeRefId) {
    match &function.type_refs[ty] {
        TypeRef::Error => s.push_str("Error"),
        TypeRef::Name(name) => s.push_str(name),
        &TypeRef::Ptr(dest) => {
            s.push_str("ptr ");
            print_type_ref(s, function, dest);
        }
        TypeRef::Unit => {
            s.push_str("unit");
        },
    }
}

fn print_expr(s: &mut String, exprs: &Arena<Expr>, id: ExprId, indent: usize) {
    match &exprs[id] {
        Expr::Missing => {
            s.push_str("<missing>");
        }
        Expr::Unit => {
            s.push_str("<unit>");
        }
        Expr::Name(name) => {
            s.push_str(name);
        }
        Expr::Number(n) => {
            _ = write!(s, "{n}");
        }
        &Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            s.push_str("if");
            s.push(' ');
            print_expr(s, exprs, cond, indent);
            s.push(' ');
            print_expr(s, exprs, then_expr, indent);
            if let Some(else_expr) = else_expr {
                s.push(' ');
                s.push_str("else");
                s.push(' ');
                print_expr(s, exprs, else_expr, indent);
            }
        }
        &Expr::Loop { body } => {
            s.push_str("loop");
            print_expr(s, exprs, body, indent)
        }
        Expr::Block { body } => {
            s.push('{');
            for stmt in body.iter() {
                print_stmt(s, exprs, stmt, indent + 1);
            }
            print_line(s, indent);
            s.push('}');
        }
        &Expr::Unary { op, operand } => {
            _ = write!(s, "{op}");
            print_expr(s, exprs, operand, indent);
        }
        &Expr::Binary { op, lhs, rhs } => {
            print_expr(s, exprs, lhs, indent);
            s.push(' ');
            _ = write!(s, "{op}");
            s.push(' ');
            print_expr(s, exprs, rhs, indent);
        }
        Expr::Break => {
            s.push_str("break");
        }
        Expr::Continue => {
            s.push_str("continue");
        }
        &Expr::Return { value } => {
            s.push_str("return");
            s.push(' ');
            print_expr(s, exprs, value, indent)
        }
        Expr::Call { callee, args } => {
            print_expr(s, exprs, *callee, indent);
            s.push('(');
            for (i, arg) in args.iter().copied().enumerate() {
                if i > 0 {
                    s.push(',');
                    s.push(' ');
                }
                print_expr(s, exprs, arg, indent);
            }
            s.push(')');
        }
        &Expr::Index { base, index } => {
            print_expr(s, exprs, base, indent);
            s.push('[');
            print_expr(s, exprs, index, indent);
            s.push(']');
        }
        Expr::Field { base, name } => {
            print_expr(s, exprs, *base, indent);
            s.push('.');
            s.push_str(name);
        }
    }
}

fn print_stmt(s: &mut String, exprs: &Arena<Expr>, stmt: &Stmt, indent: usize) {
    print_line(s, indent);
    match stmt {
        Stmt::Let(_, _) => todo!(),
        &Stmt::Expr(it) => {
            print_expr(s, exprs, it, indent);
        }
    }
}

fn print_line(s: &mut String, indent: usize) {
    s.push('\n');
    s.extend(std::iter::repeat(' ').take(indent * 4));
}

fn print_name(s: &mut String, name: &Name) {
    match name {
        Name::Missing => s.push_str("<missing>"),
        Name::Present(it) => s.push_str(it),
    }
}
