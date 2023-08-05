#![warn(unreachable_pub)]

mod lower;
mod pretty;

pub use pretty::print_function;

use core::fmt;
use la_arena::{Arena, Idx};
use lower::lower_function;
use std::{collections::HashMap, ops::Index};
use syntax::ast;

pub type ExprId = Idx<Expr>;
pub type TypeId = Idx<Type>;
pub type TypeRefId = Idx<TypeRef>;

#[derive(Debug)]
pub struct Function {
    pub name: Name,
    pub type_refs: Arena<TypeRef>,
    pub return_ty: TypeRefId,
    pub param_tys: Box<[TypeRefId]>,
    pub body: FunctionBody,
}

#[derive(Debug)]
pub struct FunctionBody {
    pub param_names: Box<[Name]>,
    pub exprs: Arena<Expr>,
    pub expr: Idx<Expr>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Name {
    Missing,
    Present(String),
}

impl From<Option<String>> for Name {
    fn from(value: Option<String>) -> Self {
        value.map(Name::Present).unwrap_or(Name::Missing)
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        match self {
            Name::Missing => false,
            Name::Present(name) => name == other,
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Missing,
    Unit,
    Name(String),
    Number(u64),
    If {
        cond: ExprId,
        then_expr: ExprId,
        else_expr: Option<ExprId>,
    },
    Loop {
        body: ExprId,
    },
    Block {
        body: Box<[Stmt]>,
    },
    Unary {
        op: UnaryOp,
        operand: ExprId,
    },
    Binary {
        op: BinaryOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Break,
    Continue,
    Return {
        value: ExprId,
    },
    Call {
        callee: ExprId,
        args: Box<[ExprId]>,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Field {
        base: ExprId,
        name: Option<String>,
    },
}

#[derive(Debug)]
pub enum TypeRef {
    Error,
    Name(String),
    Ptr(TypeRefId),
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Lte,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::Add => f.write_str("+"),
            BinaryOp::Sub => f.write_str("-"),
            BinaryOp::Lte => f.write_str("<="),
        }
    }
}

#[derive(Debug)]
pub enum Stmt {
    Let(Name, ExprId),
    Expr(ExprId),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Type {
    Error,
    Never,
    Unit,
    Uint32,
    Ptr(TypeId),
    GenericFn {
        ret_ty: TypeId,
        param_tys: Box<[TypeId]>,
    },
    SpecificFn {
        name: Name,
        ret_ty: TypeId,
        param_tys: Box<[TypeId]>,
    },
}

#[derive(Debug)]
pub struct ItemTree {
    items: Arena<Item>,
}

impl ItemTree {
    pub fn items(&self) -> &Arena<Item> {
        &self.items
    }
}

#[derive(Debug)]
pub enum Item {
    Function(Function),
}

pub fn items(file: ast::File) -> ItemTree {
    ItemTree {
        items: file
            .items()
            .map(|item| match item {
                ast::Item::FnItem(it) => Item::Function(lower_function(it)),
                ast::Item::EnumItem(_) => todo!(),
                ast::Item::UnionItem(_) => todo!(),
                ast::Item::StructItem(_) => todo!(),
                ast::Item::VariantItem(_) => todo!(),
                ast::Item::ConstantItem(_) => todo!(),
            })
            .collect(),
    }
}

#[derive(Default, Debug)]
pub struct Db {
    types: Arena<Type>,
    cache: HashMap<Type, TypeId>,
}

impl Db {
    fn get_type(&mut self, key: Type) -> TypeId {
        self.cache.get(&key).copied().unwrap_or_else(|| {
            let ty = self.types.alloc(key.clone());
            self.cache.insert(key, ty);
            ty
        })
    }
}

impl Index<TypeId> for Db {
    type Output = Type;

    fn index(&self, id: TypeId) -> &Self::Output {
        &self.types[id]
    }
}

#[derive(Debug)]
pub struct InferenceResult {
    pub param_tys: Box<[TypeId]>,
    pub return_ty: TypeId,
    pub exprs: HashMap<ExprId, TypeId>,
}

pub fn infer(db: &mut Db, items: &ItemTree, func: &Function) -> InferenceResult {
    let mut ctx = InferCtx {
        db,
        items,
        func,
        exprs: HashMap::new(),
    };
    let param_tys = func
        .param_tys
        .iter()
        .map(|&ty| lower_type_ref(&mut ctx, ty))
        .collect::<Vec<TypeId>>()
        .into_boxed_slice();
    let return_ty = lower_type_ref(&mut ctx, func.return_ty);
    infer_expr(&mut ctx, func.body.expr);

    InferenceResult {
        return_ty,
        param_tys,
        exprs: ctx.exprs,
    }
}

struct InferCtx<'a> {
    db: &'a mut Db,
    items: &'a ItemTree,
    func: &'a Function,
    exprs: HashMap<ExprId, TypeId>,
}

fn infer_expr(ctx: &mut InferCtx, expr: ExprId) -> TypeId {
    let type_id = match &ctx.func.body.exprs[expr] {
        Expr::Missing => ctx.db.get_type(Type::Error),
        Expr::Unit => ctx.db.get_type(Type::Unit),
        Expr::Name(name) => {
            let item_ty = ctx
                .items
                .items
                .values()
                .find_map(|item| match item {
                    Item::Function(func) => match &func.name {
                        Name::Present(func_name) if func_name == name => Some(func),
                        _ => None,
                    },
                })
                .map(|func| Type::SpecificFn {
                    name: func.name.clone(),
                    ret_ty: lower_type_ref(ctx, func.return_ty),
                    param_tys: func
                        .param_tys
                        .iter()
                        .map(|&ty| lower_type_ref(ctx, ty))
                        .collect::<Vec<TypeId>>()
                        .into_boxed_slice(),
                })
                .map(|ty| ctx.db.get_type(ty));
            let param_ty = ctx
                .func
                .body
                .param_names
                .iter()
                .enumerate()
                .find(|&(_, it)| it == name.as_str())
                .map(|(i, _)| lower_type_ref(ctx, ctx.func.param_tys[i]));
            param_ty
                .or(item_ty)
                .unwrap_or_else(|| ctx.db.get_type(Type::Error))
        }
        Expr::Number(_) => ctx.db.get_type(Type::Uint32),
        &Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr(ctx, cond);
            infer_expr(ctx, then_expr);
            else_expr.map(|expr| infer_expr(ctx, expr));
            ctx.db.get_type(Type::Unit)
        }
        &Expr::Loop { body } => {
            infer_expr(ctx, body);
            ctx.db.get_type(Type::Never)
        }
        Expr::Block { body } => {
            for stmt in body.iter() {
                match stmt {
                    Stmt::Let(_, _) => todo!(),
                    &Stmt::Expr(expr) => {
                        infer_expr(ctx, expr);
                    }
                }
            }
            ctx.db.get_type(Type::Unit)
        }
        &Expr::Unary { op: _, operand } => {
            let operand_ty = infer_expr(ctx, operand);
            operand_ty
        }
        &Expr::Binary { op: _, lhs, rhs } => {
            let lhs_ty = infer_expr(ctx, lhs);
            let _rhs_ty = infer_expr(ctx, rhs);
            lhs_ty
        }
        Expr::Break => ctx.db.get_type(Type::Never),
        Expr::Continue => ctx.db.get_type(Type::Never),
        &Expr::Return { value } => {
            infer_expr(ctx, value);
            ctx.db.get_type(Type::Never)
        }
        Expr::Call { callee, args } => {
            let callee_ty = infer_expr(ctx, *callee);
            let &Type::SpecificFn { ret_ty, .. } = &ctx.db.types[callee_ty] else {
                return ctx.db.get_type(Type::Error);
            };
            for &arg in args.iter() {
                infer_expr(ctx, arg);
            }
            ret_ty
        }
        &Expr::Index { base, index: _ } => {
            infer_expr(ctx, base);

            ctx.db.get_type(Type::Error)
        }
        Expr::Field { base, name: _ } => {
            infer_expr(ctx, *base);
            ctx.db.get_type(Type::Error)
        }
    };
    ctx.exprs.insert(expr, type_id);
    type_id
}

fn lower_type_ref(ctx: &mut InferCtx, ty: TypeRefId) -> TypeId {
    match &ctx.func.type_refs[ty] {
        TypeRef::Error => ctx.db.get_type(Type::Error),
        TypeRef::Name(name) => match name.as_str() {
            "u32" => ctx.db.get_type(Type::Uint32),
            _ => ctx.db.get_type(Type::Error),
        },
        &TypeRef::Ptr(dest) => {
            let dest_ty = lower_type_ref(ctx, dest);
            ctx.db.get_type(Type::Ptr(dest_ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let file = syntax::parse_file(
            "
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = items(file.clone());
        let mut db = Db::default();
        for item in items.items.values() {
            match item {
                Item::Function(func) => {
                    let _result = infer(&mut db, &items, func);
                    dbg!(&db);
                    eprintln!("{}", print_function(func));
                }
            }
        }
    }
}
