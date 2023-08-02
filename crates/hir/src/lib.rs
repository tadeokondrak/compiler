#![warn(unreachable_pub)]

mod lower;
mod pretty;

use core::fmt;
use la_arena::{Arena, Idx};
use lower::lower_function;
use std::collections::HashMap;
use syntax::ast;

type ExprId = Idx<Expr>;
type TypeId = Idx<Type>;
type TypeRefId = Idx<TypeRef>;

#[derive(Debug)]
pub struct Function {
    pub name: Name,
    pub exprs: Arena<Expr>,
    pub type_refs: Arena<TypeRef>,
    pub return_ty: TypeRefId,
    pub param_tys: Box<[TypeRefId]>,
    pub body: Idx<Expr>,
}

#[derive(Debug)]
pub enum Name {
    Missing,
    Present(String),
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
        else_expr: ExprId,
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
        name: String,
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
    Let(String, ExprId),
    Expr(ExprId),
}
#[derive(Debug, PartialEq, Eq, Hash, Clone)]

pub enum Type {
    Error,
    Never,
    Unit,
    Uint32,
    Ptr(TypeId),
    Fn {
        ret_ty: TypeId,
        param_tys: Box<[TypeId]>,
    },
}

type ItemId = Idx<Item>;

#[derive(Debug)]
struct ItemTree {
    items: Arena<Item>,
    top_level: Box<[ItemId]>,
}

#[derive(Debug)]
enum Item {
    Function(Function),
    // Block
}

fn items(file: ast::File) -> ItemTree {
    ItemTree {
        items: file
            .items()
            .map(|item| match item {
                ast::Item::LetItem(_) => todo!(),
                ast::Item::FnItem(it) => Item::Function(lower_function(it)),
                ast::Item::EnumItem(_) => todo!(),
                ast::Item::UnionItem(_) => todo!(),
                ast::Item::StructItem(_) => todo!(),
                ast::Item::VariantItem(_) => todo!(),
                ast::Item::ConstantItem(_) => todo!(),
            })
            .collect(),
        top_level: Box::new([]),
    }
}

#[derive(Default, Debug)]
struct Db {
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

#[derive(Debug)]
pub struct InferenceResult {
    param_tys: Box<[TypeId]>,
    return_ty: TypeId,
}

fn infer(db: &mut Db, items: &ItemTree, func: &Function) -> InferenceResult {
    let param_tys = func
        .param_tys
        .iter()
        .map(|&ty| lower_type_ref(db, func, ty))
        .collect::<Vec<TypeId>>()
        .into_boxed_slice();
    let return_ty = lower_type_ref(db, func, func.return_ty);
    infer_expr(db, items, func, func.body);

    InferenceResult {
        return_ty,
        param_tys,
    }
}

fn lookup_name_in_func(items: &ItemTree, func: &Function) {}

fn infer_expr(db: &mut Db, items: &ItemTree, func: &Function, expr: ExprId) -> TypeId {
    match &func.exprs[expr] {
        Expr::Missing => db.get_type(Type::Error),
        Expr::Unit => db.get_type(Type::Unit),
        Expr::Name(name) => {
            let ty = items
                .items
                .values()
                .find_map(|item| match item {
                    Item::Function(func) => match &func.name {
                        Name::Present(func_name) if func_name == name => Some(func),
                        _ => None,
                    },
                })
                .map(|func| Type::Fn {
                    ret_ty: lower_type_ref(db, func, func.return_ty),
                    param_tys: func
                        .param_tys
                        .iter()
                        .map(|&ty| lower_type_ref(db, func, ty))
                        .collect::<Vec<TypeId>>()
                        .into_boxed_slice(),
                })
                .unwrap_or(Type::Error);
            db.get_type(ty)
        }
        Expr::Number(_) => db.get_type(Type::Uint32),
        &Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr(db, items, func, cond);
            infer_expr(db, items, func, then_expr);
            infer_expr(db, items, func, else_expr);
            db.get_type(Type::Unit)
        }
        &Expr::Loop { body } => {
            infer_expr(db, items, func, body);
            db.get_type(Type::Never)
        }
        Expr::Block { body } => {
            for stmt in body.iter() {
                match stmt {
                    Stmt::Let(_, _) => todo!(),
                    &Stmt::Expr(expr) => {
                        infer_expr(db, items, func, expr);
                    }
                }
            }
            db.get_type(Type::Unit)
        }
        &Expr::Unary { op: _, operand } => {
            let operand_ty = infer_expr(db, items, func, operand);
            operand_ty
        }
        &Expr::Binary { op: _, lhs, rhs } => {
            let lhs_ty = infer_expr(db, items, func, lhs);
            let _rhs_ty = infer_expr(db, items, func, rhs);
            lhs_ty
        }
        Expr::Break => db.get_type(Type::Never),
        Expr::Continue => db.get_type(Type::Never),
        &Expr::Return { value } => {
            infer_expr(db, items, func, value);
            db.get_type(Type::Never)
        }
        Expr::Call { callee, args: _ } => {
            let callee_ty = infer_expr(db, items, func, *callee);
            let &Type::Fn { ret_ty, .. } = &db.types[callee_ty] else {
                return db.get_type(Type::Error);
            };
            ret_ty
        }
        &Expr::Index { base, index: _ } => {
            infer_expr(db, items, func, base);

            db.get_type(Type::Error)
        }
        Expr::Field { base, name: _ } => {
            infer_expr(db, items, func, *base);
            db.get_type(Type::Error)
        }
    }
}

fn lower_type_ref(db: &mut Db, func: &Function, ty: TypeRefId) -> TypeId {
    match &func.type_refs[ty] {
        TypeRef::Error => db.get_type(Type::Error),
        TypeRef::Name(name) => match name.as_str() {
            "u32" => db.get_type(Type::Uint32),
            _ => db.get_type(Type::Error),
        },
        &TypeRef::Ptr(dest) => {
            let dest_ty = lower_type_ref(db, func, dest);
            db.get_type(Type::Ptr(dest_ty))
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
    if n <= 1 {
        return 1
    }
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = items(file.clone());
        let mut db = Db::default();
        for item in items.items.values() {
            match item {
                Item::Function(func) => {
                    let result = infer(&mut db, &items, func);
                    dbg!(&db);
                }
            }
        }
    }
}
