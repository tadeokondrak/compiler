#![warn(unreachable_pub)]

mod lower;
mod pretty;

use la_arena::{Arena, Idx};
use std::{collections::HashMap, ops::Index};
use syntax::{ast, AstPtr, BinaryOp, UnaryOp};

pub use lower::{lower_function, lower_function_body, lower_struct};
pub use pretty::print_function;

pub type ExprId = Idx<Expr>;
pub type TypeId = Idx<Type>;
pub type TypeRefId = Idx<TypeRef>;

#[derive(Debug)]
pub struct Function {
    pub ast: AstPtr<ast::FnItem>,
    pub name: Name,
    pub type_refs: Arena<TypeRef>,
    pub return_ty: TypeRefId,
    pub param_tys: Box<[TypeRefId]>,
}

#[derive(Debug)]
pub struct Struct {
    pub ast: AstPtr<ast::StructItem>,
    pub name: Name,
    pub type_refs: Arena<TypeRef>,
    pub fields: Box<[StructField]>,
}

#[derive(Debug)]
pub struct StructField {
    pub name: Name,
    pub ty: TypeRefId,
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
    Bool,
    Int(Signed, IntSize),
    Ptr(TypeId),
    // The size of values of this type is infinite (it cannot exist at runtime).
    // However pointers to values of this type can exist.
    GenericFn {
        ret_ty: TypeId,
        param_tys: Box<[TypeId]>,
    },
    // The size of values of this type is zero.
    // This can only ever be one function.
    SpecificFn {
        name: Name,
        ret_ty: TypeId,
        param_tys: Box<[TypeId]>,
    },
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Signed {
    Yes,
    No,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    SizePtr,
}

#[derive(Debug)]
pub struct Items {
    items: Arena<Item>,
}

impl Items {
    pub fn items(&self) -> &Arena<Item> {
        &self.items
    }
}

#[derive(Debug)]
pub enum Item {
    Function(Function),
    Struct(Struct),
}

pub fn file_items(file: ast::File) -> Items {
    Items {
        items: file
            .items()
            .map(|item| match item {
                ast::Item::FnItem(it) => Item::Function(lower_function(it)),
                ast::Item::EnumItem(_) => todo!(),
                ast::Item::UnionItem(_) => todo!(),
                ast::Item::StructItem(it) => Item::Struct(lower_struct(it)),
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
    fn intern_type(&mut self, key: Type) -> TypeId {
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

pub fn infer(db: &mut Db, items: &Items, func: &Function, body: &FunctionBody) -> InferenceResult {
    let mut ctx = InferCtx {
        db,
        items,
        func,
        body,
        exprs: HashMap::new(),
    };
    let param_tys = func
        .param_tys
        .iter()
        .map(|&ty| lower_type_ref(&mut ctx, ty))
        .collect::<Vec<TypeId>>()
        .into_boxed_slice();
    let return_ty = lower_type_ref(&mut ctx, func.return_ty);
    infer_expr(&mut ctx, body.expr);

    InferenceResult {
        return_ty,
        param_tys,
        exprs: ctx.exprs,
    }
}

struct InferCtx<'a> {
    db: &'a mut Db,
    items: &'a Items,
    func: &'a Function,
    body: &'a FunctionBody,
    exprs: HashMap<ExprId, TypeId>,
}

fn infer_expr(ctx: &mut InferCtx, expr: ExprId) -> TypeId {
    let type_id = match &ctx.body.exprs[expr] {
        Expr::Missing => ctx.db.intern_type(Type::Error),
        Expr::Unit => ctx.db.intern_type(Type::Unit),
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
                    Item::Struct(_) => None,
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
                .map(|ty| ctx.db.intern_type(ty));
            let param_ty = ctx
                .body
                .param_names
                .iter()
                .enumerate()
                .find(|&(_, it)| it == name.as_str())
                .map(|(i, _)| lower_type_ref(ctx, ctx.func.param_tys[i]));
            param_ty
                .or(item_ty)
                .unwrap_or_else(|| ctx.db.intern_type(Type::Error))
        }
        Expr::Number(_) => ctx.db.intern_type(Type::Int(Signed::No, IntSize::Size32)),
        &Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr(ctx, cond);
            infer_expr(ctx, then_expr);
            else_expr.map(|expr| infer_expr(ctx, expr));
            ctx.db.intern_type(Type::Unit)
        }
        &Expr::Loop { body } => {
            infer_expr(ctx, body);
            ctx.db.intern_type(Type::Never)
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
            ctx.db.intern_type(Type::Unit)
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
        Expr::Break => ctx.db.intern_type(Type::Never),
        Expr::Continue => ctx.db.intern_type(Type::Never),
        &Expr::Return { value } => {
            infer_expr(ctx, value);
            ctx.db.intern_type(Type::Never)
        }
        Expr::Call { callee, args } => {
            let callee_ty = infer_expr(ctx, *callee);
            let &Type::SpecificFn { ret_ty, .. } = &ctx.db.types[callee_ty] else {
                return ctx.db.intern_type(Type::Error);
            };
            for &arg in args.iter() {
                infer_expr(ctx, arg);
            }
            ret_ty
        }
        &Expr::Index { base, index: _ } => {
            infer_expr(ctx, base);

            ctx.db.intern_type(Type::Error)
        }
        Expr::Field { base, name: _ } => {
            infer_expr(ctx, *base);
            ctx.db.intern_type(Type::Error)
        }
    };
    ctx.exprs.insert(expr, type_id);
    type_id
}

fn lower_type_ref(ctx: &mut InferCtx, ty: TypeRefId) -> TypeId {
    match &ctx.func.type_refs[ty] {
        TypeRef::Error => ctx.db.intern_type(Type::Error),
        TypeRef::Name(name) => match name.as_str() {
            "u8" => ctx.db.intern_type(Type::Int(Signed::No, IntSize::Size8)),
            "u16" => ctx.db.intern_type(Type::Int(Signed::No, IntSize::Size16)),
            "u32" => ctx.db.intern_type(Type::Int(Signed::No, IntSize::Size32)),
            "u64" => ctx.db.intern_type(Type::Int(Signed::No, IntSize::Size64)),
            "usize" => ctx.db.intern_type(Type::Int(Signed::No, IntSize::SizePtr)),
            "i8" => ctx.db.intern_type(Type::Int(Signed::Yes, IntSize::Size8)),
            "i16" => ctx.db.intern_type(Type::Int(Signed::Yes, IntSize::Size16)),
            "i32" => ctx.db.intern_type(Type::Int(Signed::Yes, IntSize::Size32)),
            "i64" => ctx.db.intern_type(Type::Int(Signed::Yes, IntSize::Size64)),
            "isize" => ctx.db.intern_type(Type::Int(Signed::Yes, IntSize::SizePtr)),
            _ => ctx.db.intern_type(Type::Error),
        },
        &TypeRef::Ptr(dest) => {
            let dest_ty = lower_type_ref(ctx, dest);
            ctx.db.intern_type(Type::Ptr(dest_ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syntax::AstNode;

    #[test]
    fn test_infer() {
        let file = syntax::parse_file(
            "
struct Numbers {
    x i32;
    y i32;
}
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = file_items(file.clone());
        let mut db = Db::default();
        for item in items.items.values() {
            match item {
                Item::Function(func) => {
                    let body = lower_function_body(func.ast.to_node(file.syntax()));
                    let _result = infer(&mut db, &items, func, &body);
                    dbg!(&db);
                    eprintln!("{}", print_function(func, &body));
                }
                Item::Struct(_structure) => {}
            }
        }
    }
}
