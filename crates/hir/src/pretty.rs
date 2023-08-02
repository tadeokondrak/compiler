use crate::{Expr, ExprId, Function, Name, Stmt};
use la_arena::Arena;
use std::fmt::Write;

pub(crate) fn print_function(s: &mut String, function: &Function) {
    s.push_str("fn");
    s.push(' ');
    print_name(s, &function.name);
    s.push('(');
    s.push(')');
    s.push(' ');
    print_expr(s, &function.exprs, function.body, 0);
}

fn print_expr(s: &mut String, exprs: &Arena<Expr>, id: ExprId, indent: usize) {
    match &exprs[id] {
        Expr::Missing => {
            s.push_str("todo: Missing");
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
            s.push(' ');
            s.push_str("else");
            s.push(' ');
            print_expr(s, exprs, else_expr, indent);
        }
        Expr::Loop { body: _ } => {
            s.push_str("todo: Loop");
        }
        Expr::Block { body } => {
            s.push('{');
            for stmt in body.iter() {
                print_stmt(s, exprs, stmt, indent + 1);
            }
            print_line(s, indent);
            s.push('}');
        }
        Expr::Unary { op: _, operand: _ } => {
            s.push_str("todo: Unary");
        }
        &Expr::Binary { op, lhs, rhs } => {
            print_expr(s, exprs, lhs, indent);
            s.push(' ');
            _ = write!(s, "{op}");
            s.push(' ');
            print_expr(s, exprs, rhs, indent);
        }
        Expr::Break => {
            s.push_str("todo: Break");
        }
        Expr::Continue => {
            s.push_str("todo: Continue");
        }
        &Expr::Return { value } => {
            s.push_str("return");
            s.push(' ');
            print_expr(s, exprs, value, indent)
        }
        Expr::Call {
            callee,
            args,
        } => {
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
        Expr::Index { base: _, index: _ } => {
            s.push_str("todo: Index");
        }
        Expr::Field { base: _, name: _ } => {
            s.push_str("todo: Field");
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
