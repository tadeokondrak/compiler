use crate::{Expr, ExprId, Function, FunctionBody, Name, Stmt, TypeRef, TypeRefId};
use la_arena::Arena;
use syntax::ast;

#[derive(Default)]
struct Ctx {
    exprs: Arena<Expr>,
    type_refs: Arena<TypeRef>,
}

impl Ctx {
    fn alloc_expr(&mut self, expr: Expr) -> ExprId {
        self.exprs.alloc(expr)
    }

    fn alloc_type_ref(&mut self, type_ref: TypeRef) -> TypeRefId {
        self.type_refs.alloc(type_ref)
    }

    fn lower_expr_opt(&mut self, expr: Option<ast::Expr>) -> ExprId {
        match expr {
            Some(it) => self.lower_expr(it),
            None => self.alloc_expr(Expr::Missing),
        }
    }

    fn lower_expr(&mut self, expr: ast::Expr) -> la_arena::Idx<Expr> {
        match expr {
            ast::Expr::ParenExpr(it) => self.lower_expr_opt(it.inner()),
            ast::Expr::NameExpr(it) => self.alloc_expr(
                it.identifier_token()
                    .map(|it| it.text().to_owned())
                    .map(Expr::Name)
                    .unwrap_or(Expr::Missing),
            ),
            ast::Expr::LiteralExpr(it) => self.alloc_expr(
                it.number_token()
                    .and_then(|it| it.text().parse().map(Expr::Number).ok())
                    .unwrap_or(Expr::Missing),
            ),
            ast::Expr::IfExpr(it) => {
                let expr = Expr::If {
                    cond: self.lower_expr_opt(it.condition()),
                    then_expr: self.lower_expr_opt(it.then_body().map(ast::Expr::BlockExpr)),
                    else_expr: it
                        .else_body()
                        .map(ast::Expr::BlockExpr)
                        .map(|expr| self.lower_expr(expr)),
                };
                self.alloc_expr(expr)
            }
            ast::Expr::LoopExpr(_) => self.alloc_expr(Expr::Missing),
            ast::Expr::WhileExpr(_) => self.alloc_expr(Expr::Missing),
            ast::Expr::BlockExpr(it) => {
                let expr = Expr::Block {
                    body: it
                        .stmts()
                        .filter_map(|stmt| self.lower_stmt(stmt))
                        .collect::<Vec<Stmt>>()
                        .into_boxed_slice(),
                };
                self.alloc_expr(expr)
            }
            ast::Expr::UnaryExpr(_) => self.alloc_expr(Expr::Missing),
            ast::Expr::BinaryExpr(it) => {
                let expr = Expr::Binary {
                    op: it.op(),
                    lhs: self.lower_expr_opt(it.lhs()),
                    rhs: self.lower_expr_opt(it.rhs()),
                };
                self.alloc_expr(expr)
            }
            ast::Expr::BreakExpr(_) => self.alloc_expr(Expr::Break),
            ast::Expr::ReturnExpr(it) => {
                let value = self.lower_expr_opt(it.value());
                self.alloc_expr(Expr::Return { value })
            }
            ast::Expr::ContinueExpr(_) => self.alloc_expr(Expr::Continue),
            ast::Expr::CallExpr(it) => {
                let callee = self.lower_expr_opt(it.callee());
                let args = it
                    .arguments()
                    .map(|arg| self.lower_expr_opt(arg.expr()))
                    .collect::<Vec<ExprId>>()
                    .into_boxed_slice();
                self.alloc_expr(Expr::Call { callee, args })
            }
            ast::Expr::IndexExpr(it) => {
                let base = self.lower_expr_opt(it.base());
                let index = self.lower_expr_opt(it.index());
                self.alloc_expr(Expr::Index { base, index })
            }
            ast::Expr::FieldExpr(it) => {
                let base = self.lower_expr_opt(it.base());
                self.alloc_expr(Expr::Field {
                    base,
                    name: it.identifier_token().map(|s| s.text().to_owned()),
                })
            }
        }
    }

    fn lower_stmt(&mut self, stmt: ast::Stmt) -> Option<Stmt> {
        match stmt {
            ast::Stmt::ItemStmt(_) => None,
            ast::Stmt::ExprStmt(it) => Some(Stmt::Expr(self.lower_expr_opt(it.expr()))),
            ast::Stmt::LetStmt(it) => Some(Stmt::Let(
                it.identifier_token().map(|it| it.text().to_owned()).into(),
                self.lower_expr_opt(it.expr()),
            )),
        }
    }

    fn lower_type_ref(&mut self, ty: ast::Type) -> TypeRefId {
        match ty {
            ast::Type::ParenType(it) => self.lower_type_ref_opt(it.ty()),
            ast::Type::NameType(it) => self.alloc_type_ref(
                it.identifier_token()
                    .map(|it| TypeRef::Name(it.text().to_owned()))
                    .unwrap_or(TypeRef::Error),
            ),
            ast::Type::SliceType(_) => todo!(),
            ast::Type::PointerType(it) => {
                let dest_type = self.lower_type_ref_opt(it.dest_ty());
                self.alloc_type_ref(TypeRef::Ptr(dest_type))
            }
        }
    }

    fn lower_type_ref_opt(&mut self, ty: Option<ast::Type>) -> TypeRefId {
        match ty {
            Some(it) => self.lower_type_ref(it),
            None => self.alloc_type_ref(TypeRef::Error),
        }
    }

    fn lower_function(mut self, func: ast::FnItem) -> Function {
        let name = func
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let return_ty = self.lower_type_ref_opt(func.return_ty());
        let body = self.lower_expr_opt(func.body().map(ast::Expr::BlockExpr));

        let param_tys = func
            .parameters()
            .map(|param| self.lower_type_ref_opt(param.ty()))
            .collect::<Vec<TypeRefId>>()
            .into_boxed_slice();

        let param_names = func
            .parameters()
            .map(|param| {
                param
                    .identifier_token()
                    .map(|it| it.text().to_owned())
                    .into()
            })
            .collect::<Vec<Name>>()
            .into_boxed_slice();

        Function {
            type_refs: self.type_refs,
            return_ty,
            param_tys,
            name,
            body: FunctionBody {
                param_names,
                exprs: self.exprs,
                expr: body,
            },
        }
    }
}

pub(crate) fn lower_function(func: ast::FnItem) -> Function {
    Ctx::default().lower_function(func)
}
