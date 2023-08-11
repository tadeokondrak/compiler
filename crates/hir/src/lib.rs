#![warn(unreachable_pub)]

mod infer;
mod lower;
mod pretty;

use la_arena::{Arena, Idx};
use std::{collections::HashMap, fmt::Write, ops::Index};
use syntax::{ast, AstPtr, BinaryOp, UnaryOp};

pub use infer::{infer, InferenceResult};
pub use lower::{lower_const, lower_enum, lower_function, lower_function_body, lower_record};
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
pub struct Record {
    pub ast: AstPtr<ast::Item>,
    pub name: Name,
    pub type_refs: Arena<TypeRef>,
    pub fields: Box<[RecordField]>,
}

#[derive(Debug)]
pub struct Const {
    pub ast: AstPtr<ast::ConstItem>,
    pub name: Name,
    pub type_refs: Arena<TypeRef>,
    pub ty: TypeRefId,
}

#[derive(Debug)]
pub struct Enum {
    pub ast: AstPtr<ast::EnumItem>,
    pub name: Name,
    pub variants: Box<[EnumVariant]>,
}

#[derive(Debug)]
pub struct RecordField {
    pub name: Name,
    pub ty: TypeRefId,
}

#[derive(Debug)]
pub struct EnumVariant {
    pub name: Name,
}

#[derive(Debug)]
pub struct Body {
    pub param_names: Box<[Name]>,
    pub expr_map: HashMap<ExprId, AstPtr<ast::Expr>>,
    pub exprs: Arena<Expr>,
    pub expr: ExprId,
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
        name: String,
    },
}

#[derive(Debug)]
pub enum TypeRef {
    Error,
    Unit,
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
    Record(RecordId),
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

#[derive(Debug, Default)]
pub struct Items {
    items: Vec<ItemId>,
    enums: Arena<Enum>,
    consts: Arena<Const>,
    records: Arena<Record>,
    functions: Arena<Function>,
    by_name: HashMap<String, ItemId>,
}

type EnumId = Idx<Enum>;
type ConstId = Idx<Const>;
type RecordId = Idx<Record>;
type FunctionId = Idx<Function>;

impl Items {
    pub fn items(&self) -> &[ItemId] {
        &self.items
    }
}

impl Index<FunctionId> for Items {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index]
    }
}

impl Index<RecordId> for Items {
    type Output = Record;

    fn index(&self, index: RecordId) -> &Self::Output {
        &self.records[index]
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ItemId {
    Function(FunctionId),
    Enum(EnumId),
    Record(RecordId),
    Const(ConstId),
}

pub fn file_items(file: ast::File) -> Items {
    let mut items = Items::default();
    for syntax in file.items() {
        match syntax {
            ast::Item::FnItem(it) => {
                let lowered = lower_function(it);
                let lowered = items.functions.alloc(lowered);
                let lowered_id = ItemId::Function(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items.functions[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::EnumItem(it) => {
                let lowered = lower_enum(it);
                let lowered = items.enums.alloc(lowered);
                let lowered_id = ItemId::Enum(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items.enums[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::RecordItem(it) => {
                let lowered = lower_record(it);
                let lowered = items.records.alloc(lowered);
                let lowered_id = ItemId::Record(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items.records[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::ConstItem(it) => {
                let lowered = lower_const(it);
                let lowered = items.consts.alloc(lowered);
                let lowered_id = ItemId::Const(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items.consts[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
        }
    }
    items
}

#[derive(Default, Debug)]
pub struct Analysis {
    types: Arena<Type>,
    type_cache: HashMap<Type, TypeId>,
}

impl Analysis {
    fn intern_type(&mut self, key: Type) -> TypeId {
        self.type_cache.get(&key).copied().unwrap_or_else(|| {
            let ty = self.types.alloc(key.clone());
            self.type_cache.insert(key, ty);
            ty
        })
    }
}

impl Index<TypeId> for Analysis {
    type Output = Type;

    fn index(&self, id: TypeId) -> &Self::Output {
        &self.types[id]
    }
}

fn lower_type_ref(
    analysis: &mut Analysis,
    items: &Items,
    type_refs: &Arena<TypeRef>,
    ty: TypeRefId,
) -> TypeId {
    match &type_refs[ty] {
        TypeRef::Error => analysis.intern_type(Type::Error),
        TypeRef::Name(name) => match items.by_name.get(name) {
            Some(&ItemId::Function(func_id)) => {
                let func = &items[func_id];
                let ret_ty = lower_type_ref(analysis, items, type_refs, func.return_ty);
                let param_tys = func
                    .param_tys
                    .iter()
                    .copied()
                    .map(|ty| lower_type_ref(analysis, items, type_refs, ty))
                    .collect();
                analysis.intern_type(Type::SpecificFn {
                    name: func.name.clone(),
                    ret_ty,
                    param_tys,
                })
            }
            Some(&ItemId::Record(record_id)) => analysis.intern_type(Type::Record(record_id)),
            Some(_) => todo!(),
            None => match name.as_str() {
                "u8" => analysis.intern_type(Type::Int(Signed::No, IntSize::Size8)),
                "u16" => analysis.intern_type(Type::Int(Signed::No, IntSize::Size16)),
                "u32" => analysis.intern_type(Type::Int(Signed::No, IntSize::Size32)),
                "u64" => analysis.intern_type(Type::Int(Signed::No, IntSize::Size64)),
                "usize" => analysis.intern_type(Type::Int(Signed::No, IntSize::SizePtr)),
                "i8" => analysis.intern_type(Type::Int(Signed::Yes, IntSize::Size8)),
                "i16" => analysis.intern_type(Type::Int(Signed::Yes, IntSize::Size16)),
                "i32" => analysis.intern_type(Type::Int(Signed::Yes, IntSize::Size32)),
                "i64" => analysis.intern_type(Type::Int(Signed::Yes, IntSize::Size64)),
                "isize" => analysis.intern_type(Type::Int(Signed::Yes, IntSize::SizePtr)),
                _ => analysis.intern_type(Type::Error),
            },
        },
        &TypeRef::Ptr(dest) => {
            let dest_ty = lower_type_ref(analysis, items, type_refs, dest);
            analysis.intern_type(Type::Ptr(dest_ty))
        }
        TypeRef::Unit => analysis.intern_type(Type::Unit),
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
struct Vec2 {
    x i32
    y i32
}
fn get_x(v Vec2) { return v.x }
fn exit(n i32)
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    exit(0)
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = file_items(file.clone());
        eprintln!("{items:#?}");
        let mut analysis = Analysis::default();
        for item in &items.items {
            match item {
                &ItemId::Function(func_id) => {
                    let func = &items.functions[func_id];
                    let body = lower_function_body(func.ast.to_node(file.syntax()));
                    let _result = infer(&mut analysis, &items, func, &body);
                    dbg!(&analysis);
                    eprintln!("{}", print_function(func, &body));
                }
                ItemId::Record(_structure) => {}
                ItemId::Const(_) => todo!(),
                ItemId::Enum(_) => todo!(),
            }
        }
    }
}

pub fn print_type(analysis: &Analysis, ty: TypeId) -> String {
    let mut s = String::new();
    print_type_(&mut s, analysis, ty);
    s
}

fn print_type_(s: &mut String, analysis: &Analysis, ty: TypeId) {
    match &analysis.types[ty] {
        Type::Error => s.push_str("(error)"),
        Type::Never => s.push_str("(never)"),
        Type::Unit => s.push_str("(unit)"),
        Type::Bool => s.push_str("bool"),
        Type::Int(Signed::No, IntSize::Size8) => s.push_str("u8"),
        Type::Int(Signed::No, IntSize::Size16) => s.push_str("u16"),
        Type::Int(Signed::No, IntSize::Size32) => s.push_str("u32"),
        Type::Int(Signed::No, IntSize::Size64) => s.push_str("u64"),
        Type::Int(Signed::No, IntSize::SizePtr) => s.push_str("usize"),
        Type::Int(Signed::Yes, IntSize::Size8) => s.push_str("i8"),
        Type::Int(Signed::Yes, IntSize::Size16) => s.push_str("i16"),
        Type::Int(Signed::Yes, IntSize::Size32) => s.push_str("i32"),
        Type::Int(Signed::Yes, IntSize::Size64) => s.push_str("i64"),
        Type::Int(Signed::Yes, IntSize::SizePtr) => s.push_str("isize"),
        &Type::Ptr(ty) => {
            s.push_str("ptr");
            s.push(' ');
            print_type_(s, analysis, ty);
        }
        Type::Record(record) => {
            _ = write!(s, "record {record:?}");
        }
        Type::GenericFn { ret_ty, param_tys } => s.push_str("Type::GenericFn"),
        Type::SpecificFn {
            name,
            ret_ty,
            param_tys,
        } => s.push_str("Type::SpecificFn"),
    }
}
