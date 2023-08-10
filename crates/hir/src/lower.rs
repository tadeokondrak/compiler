use crate::{
    Body, Const, Enum, Expr, ExprId, Function, Record, RecordField, Stmt, TypeRef, TypeRefId,
};
use la_arena::Arena;
use syntax::{ast, AstPtr};

#[derive(Default)]
struct Ctx {
    type_refs: Arena<TypeRef>,
}

#[derive(Default)]
struct BodyCtx {
    exprs: Arena<Expr>,
}

impl Ctx {
    fn alloc_type_ref(&mut self, type_ref: TypeRef) -> TypeRefId {
        self.type_refs.alloc(type_ref)
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

    fn lower_function(mut self, syntax: ast::FnItem) -> Function {
        let name = syntax
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let return_ty = syntax
            .return_ty()
            .map(|ty| self.lower_type_ref(ty))
            .unwrap_or_else(|| self.alloc_type_ref(TypeRef::Unit));

        let param_tys = syntax
            .parameters()
            .map(|param| self.lower_type_ref_opt(param.ty()))
            .collect();

        Function {
            ast: AstPtr::new(&syntax),
            type_refs: self.type_refs,
            return_ty,
            param_tys,
            name,
        }
    }

    fn lower_record(mut self, syntax: ast::RecordItem) -> Record {
        let name = syntax
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let fields = syntax
            .members()
            .map(|member| self.lower_struct_member(member))
            .collect();
        Record {
            ast: AstPtr::new(&ast::Item::RecordItem(syntax)),
            name,
            type_refs: self.type_refs,
            fields,
        }
    }

    fn lower_struct_member(&mut self, syntax: ast::Member) -> RecordField {
        let name = syntax
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let ty = self.lower_type_ref_opt(syntax.ty());
        RecordField { name, ty }
    }

    fn lower_const(mut self, syntax: ast::ConstItem) -> Const {
        let name = syntax
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let ty = self.lower_type_ref_opt(syntax.ty());
        Const {
            ast: AstPtr::new(&syntax),
            name,
            type_refs: self.type_refs,
            ty,
        }
    }

    fn lower_enum(&self, syntax: ast::EnumItem) -> Enum {
        let name = syntax
            .identifier_token()
            .map(|tok| tok.text().to_owned())
            .into();
        let variants = syntax
            .variants()
            .map(|variant| self.lower_enum_variant(variant))
            .collect();
        Enum {
            ast: AstPtr::new(&syntax),
            name,
            variants,
        }
    }

    fn lower_enum_variant(&self, _variant: ast::Variant) -> crate::EnumVariant {
        todo!()
    }
}

impl BodyCtx {
    fn alloc_expr(&mut self, expr: Expr) -> ExprId {
        self.exprs.alloc(expr)
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
            ast::Expr::LoopExpr(it) => {
                let body = self.lower_expr_opt(it.body().map(ast::Expr::BlockExpr));
                self.alloc_expr(Expr::Loop { body })
            }
            ast::Expr::WhileExpr(it) => {
                let cond = self.lower_expr_opt(it.condition());
                let then_expr = self.lower_expr_opt(it.body().map(ast::Expr::BlockExpr));
                let else_expr = Some(self.alloc_expr(Expr::Break));
                let body = self.alloc_expr(Expr::If {
                    cond,
                    then_expr,
                    else_expr,
                });
                self.alloc_expr(Expr::Loop { body })
            }
            ast::Expr::BlockExpr(it) => {
                let expr = Expr::Block {
                    body: it
                        .stmts()
                        .filter_map(|stmt| self.lower_stmt(stmt))
                        .collect(),
                };
                self.alloc_expr(expr)
            }
            ast::Expr::UnaryExpr(it) => {
                let expr = Expr::Unary {
                    op: it.op(),
                    operand: self.lower_expr_opt(it.operand()),
                };
                self.alloc_expr(expr)
            }
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
                    .collect();
                self.alloc_expr(Expr::Call { callee, args })
            }
            ast::Expr::IndexExpr(it) => {
                let base = self.lower_expr_opt(it.base());
                let index = self.lower_expr_opt(it.index());
                self.alloc_expr(Expr::Index { base, index })
            }
            ast::Expr::FieldExpr(it) => {
                let base = self.lower_expr_opt(it.base());
                match it.identifier_token() {
                    Some(name) => self.alloc_expr(Expr::Field {
                        base,
                        name: name.text().to_owned(),
                    }),
                    None => self.alloc_expr(Expr::Missing),
                }
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

    fn lower_function_body(mut self, syntax: ast::FnItem) -> Body {
        let body = self.lower_expr_opt(syntax.body().map(ast::Expr::BlockExpr));
        let param_names = syntax
            .parameters()
            .map(|param| {
                param
                    .identifier_token()
                    .map(|it| it.text().to_owned())
                    .into()
            })
            .collect();

        Body {
            param_names,
            exprs: self.exprs,
            expr: body,
        }
    }

    #[allow(unreachable_pub)]
    pub fn lower_constant_body(mut self, syntax: ast::ConstItem) -> Body {
        let body = self.lower_expr_opt(syntax.expr());
        Body {
            param_names: Box::new([]),
            exprs: self.exprs,
            expr: body,
        }
    }
}

pub fn lower_function(syntax: ast::FnItem) -> Function {
    Ctx::default().lower_function(syntax)
}

pub fn lower_record(syntax: ast::RecordItem) -> Record {
    Ctx::default().lower_record(syntax)
}

pub fn lower_const(syntax: ast::ConstItem) -> Const {
    Ctx::default().lower_const(syntax)
}

pub fn lower_enum(syntax: ast::EnumItem) -> Enum {
    Ctx::default().lower_enum(syntax)
}

pub fn lower_function_body(syntax: ast::FnItem) -> Body {
    BodyCtx::default().lower_function_body(syntax)
}

#[allow(unreachable_pub, unused)]
pub fn lower_constant_body(syntax: ast::ConstItem) -> Body {
    BodyCtx::default().lower_constant_body(syntax)
}
