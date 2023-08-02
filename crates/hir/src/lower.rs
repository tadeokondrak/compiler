use crate::{
    BinaryOp, Expr, ExprId, Function, Name, Stmt, TypeRef, TypeRefId,
};
use la_arena::Arena;
use syntax::{ast, t, AstNode, NodeOrToken};

pub(crate) fn lower_function(func: ast::FnItem) -> Function {
    let mut exprs = Arena::new();
    let mut type_refs = Arena::new();

    let name = func
        .identifier_token()
        .map(|tok| Name::Present(tok.text().to_owned()))
        .unwrap_or(Name::Missing);
    let return_ty = lower_type_ref_opt(&mut type_refs, func.return_ty());
    let body = lower_expr_opt(&mut exprs, func.body().map(ast::Expr::BlockExpr));

    let param_tys = func
        .parameters()
        .map(|param| lower_type_ref_opt(&mut type_refs, param.ty()))
        .collect::<Vec<TypeRefId>>()
        .into_boxed_slice();

    Function {
        exprs,
        type_refs,
        return_ty,
        param_tys,
        name,
        body,
    }
}

fn lower_expr_opt(exprs: &mut Arena<Expr>, expr: Option<ast::Expr>) -> ExprId {
    match expr {
        Some(it) => lower_expr(exprs, it),
        None => exprs.alloc(Expr::Missing),
    }
}

fn lower_expr(exprs: &mut Arena<Expr>, expr: ast::Expr) -> la_arena::Idx<Expr> {
    match expr {
        ast::Expr::ParenExpr(it) => lower_expr_opt(exprs, it.inner()),
        ast::Expr::NameExpr(it) => exprs.alloc(
            it.identifier_token()
                .map(|it| it.text().to_owned())
                .map(Expr::Name)
                .unwrap_or(Expr::Missing),
        ),
        ast::Expr::LiteralExpr(it) => exprs.alloc(
            it.number_token()
                .and_then(|it| it.text().parse().map(Expr::Number).ok())
                .unwrap_or(Expr::Missing),
        ),
        ast::Expr::IfExpr(it) => {
            let expr = Expr::If {
                cond: lower_expr_opt(exprs, it.condition()),
                then_expr: lower_expr_opt(exprs, it.then_body().map(ast::Expr::BlockExpr)),
                else_expr: it
                    .else_body()
                    .map(ast::Expr::BlockExpr)
                    .map(|expr| lower_expr(exprs, expr))
                    .unwrap_or_else(|| exprs.alloc(Expr::Unit)),
            };
            exprs.alloc(expr)
        }
        ast::Expr::LoopExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::WhileExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::BlockExpr(it) => {
            let expr = Expr::Block {
                body: it
                    .stmts()
                    .map(|stmt| lower_stmt(exprs, stmt))
                    .collect::<Vec<Stmt>>()
                    .into_boxed_slice(),
            };
            exprs.alloc(expr)
        }
        ast::Expr::UnaryExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::BinaryExpr(it) => {
            let op = it
                .syntax()
                .children_with_tokens()
                .filter_map(NodeOrToken::into_token)
                .filter(|it| !it.kind().is_trivia())
                .next()
                .unwrap()
                .kind();
            let op = match op {
                t!("+") => BinaryOp::Add,
                t!("-") => BinaryOp::Sub,
                t!("<=") => BinaryOp::Lte,
                _ => todo!("{op:?}"),
            };
            let expr = Expr::Binary {
                op,
                lhs: lower_expr_opt(exprs, it.lhs()),
                rhs: lower_expr_opt(exprs, it.rhs()),
            };
            exprs.alloc(expr)
        }
        ast::Expr::BreakExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::ReturnExpr(it) => {
            let value = lower_expr_opt(exprs, it.value());
            exprs.alloc(Expr::Return { value })
        }
        ast::Expr::ContinueExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::CallExpr(it) => {
            let callee = lower_expr_opt(exprs, it.callee());
            let args = it
                .arguments()
                .map(|arg| lower_expr_opt(exprs, arg.expr()))
                .collect::<Vec<ExprId>>()
                .into_boxed_slice();
            exprs.alloc(Expr::Call { callee, args })
        }
        ast::Expr::IndexExpr(_) => exprs.alloc(Expr::Missing),
        ast::Expr::FieldExpr(_) => exprs.alloc(Expr::Missing),
    }
}

fn lower_stmt(exprs: &mut Arena<Expr>, stmt: ast::Stmt) -> Stmt {
    match stmt {
        ast::Stmt::ItemStmt(_it) => {
            todo!()
        }
        ast::Stmt::ExprStmt(it) => Stmt::Expr(lower_expr_opt(exprs, it.expr())),
    }
}

fn lower_type_ref(type_refs: &mut Arena<TypeRef>, ty: ast::Type) -> TypeRefId {
    match ty {
        ast::Type::ParenType(it) => lower_type_ref_opt(type_refs, it.ty()),
        ast::Type::NameType(it) => type_refs.alloc(
            it.identifier_token()
                .map(|it| TypeRef::Name(it.text().to_owned()))
                .unwrap_or(TypeRef::Error),
        ),
        ast::Type::SliceType(_) => todo!(),
        ast::Type::PointerType(it) => {
            let dest_type = lower_type_ref_opt(type_refs, it.dest_ty());
            type_refs.alloc(TypeRef::Ptr(dest_type))
        }
    }
}

fn lower_type_ref_opt(type_refs: &mut Arena<TypeRef>, ty: Option<ast::Type>) -> TypeRefId {
    match ty {
        Some(it) => lower_type_ref(type_refs, it),
        None => type_refs.alloc(TypeRef::Error),
    }
}
