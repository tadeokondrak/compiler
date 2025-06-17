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
pub type TypeVarId = Idx<()>;
pub type TypeRefId = Idx<TypeRef>;
pub type EnumId = Idx<Enum>;
pub type ConstId = Idx<Const>;
pub type RecordId = Idx<Record>;
pub type FunctionId = Idx<Function>;

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
    Enum(EnumId),
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
    // TODO maybe the wrong place for this; we can move this into an inference-only type
    Unresolved(TypeVarId),
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

#[derive(Debug, Clone, Copy)]
pub enum ItemId {
    Function(FunctionId),
    Enum(EnumId),
    Record(RecordId),
    Const(ConstId),
}

enum NameResolution {
    BuiltinType(BuiltinType),
    Item(ItemId),
}

enum BuiltinType {
    Int(Signed, IntSize),
}

#[derive(Default, Debug)]
pub struct Analysis {
    types: Arena<Type>,
    type_cache: HashMap<Type, TypeId>,
}

macro_rules! impl_index {
    ($($base:ty { $($field: ident : $t:ty),* $(,)? }),* $(,)?) => {
        $($(
            impl Index<Idx<$t>> for $base {
                type Output = $t;

                fn index(&self, index: Idx<$t>) -> &$t {
                    &self.$field[index]
                }
            }
        )*)*
    };
}

impl From<Option<String>> for Name {
    fn from(value: Option<String>) -> Self {
        value.map(Name::Present).unwrap_or(Name::Missing)
    }
}

impl_index! {
    Items {
        enums: Enum,
        consts: Const,
        functions: Function,
        records: Record,
    },
    Analysis {
        types: Type,
    },
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        match self {
            Name::Missing => false,
            Name::Present(name) => name == other,
        }
    }
}

impl Items {
    pub fn items(&self) -> &[ItemId] {
        &self.items
    }
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
                if let Name::Present(name) = &items[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::EnumItem(it) => {
                let lowered = lower_enum(it);
                let lowered = items.enums.alloc(lowered);
                let lowered_id = ItemId::Enum(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::RecordItem(it) => {
                let lowered = lower_record(it);
                let lowered = items.records.alloc(lowered);
                let lowered_id = ItemId::Record(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
            ast::Item::ConstItem(it) => {
                let lowered = lower_const(it);
                let lowered = items.consts.alloc(lowered);
                let lowered_id = ItemId::Const(lowered);
                items.items.push(lowered_id);
                if let Name::Present(name) = &items[lowered].name {
                    items.by_name.insert(name.clone(), lowered_id);
                }
            }
        }
    }
    items
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

fn lower_type_ref(
    analysis: &mut Analysis,
    items: &Items,
    type_refs: &Arena<TypeRef>,
    ty: TypeRefId,
) -> TypeId {
    match &type_refs[ty] {
        TypeRef::Error => analysis.intern_type(Type::Error),
        TypeRef::Name(name) => match resolve_name(items, name) {
            Some(NameResolution::BuiltinType(BuiltinType::Int(signed, size))) => {
                analysis.intern_type(Type::Int(signed, size))
            }
            Some(NameResolution::Item(ItemId::Function(func_id))) => {
                func_type(items, analysis, type_refs, func_id)
            }
            Some(NameResolution::Item(ItemId::Enum(enum_id))) => {
                analysis.intern_type(Type::Enum(enum_id))
            }
            Some(NameResolution::Item(ItemId::Record(record_id))) => {
                analysis.intern_type(Type::Record(record_id))
            }
            Some(NameResolution::Item(ItemId::Const(_const_id))) => {
                todo!()
            }
            None => analysis.intern_type(Type::Error),
        },
        &TypeRef::Ptr(dest) => {
            let dest_ty = lower_type_ref(analysis, items, type_refs, dest);
            analysis.intern_type(Type::Ptr(dest_ty))
        }
        TypeRef::Unit => analysis.intern_type(Type::Unit),
    }
}

#[rustfmt::skip]
fn resolve_name(
    items: &Items,
    name: &str,
) -> Option<NameResolution> {
    match items.by_name.get(name) {
        Some(&item_id) => Some(NameResolution::Item(item_id)),
        None => match name {
            "u8" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::No, IntSize::Size8))),
            "u16" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::No, IntSize::Size16))),
            "u32" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::No, IntSize::Size32))),
            "u64" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::No, IntSize::Size64))),
            "usize" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::No, IntSize::SizePtr))),
            "i8" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::Yes, IntSize::Size8))),
            "i16" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::Yes, IntSize::Size16))),
            "i32" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::Yes, IntSize::Size32))),
            "i64" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::Yes, IntSize::Size64))),
            "isize" => Some(NameResolution::BuiltinType(BuiltinType::Int(Signed::Yes, IntSize::SizePtr))),
            _ => None,
        },
    }
}

fn func_type(
    items: &Items,
    analysis: &mut Analysis,
    type_refs: &Arena<TypeRef>,
    func_id: Idx<Function>,
) -> TypeId {
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

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};
    use syntax::AstNode;

    fn check(src: &str, expected: Expect) {
        let file = syntax::parse_file(src);
        let items = file_items(file.clone());
        let mut analysis = Analysis::default();
        let mut out = String::new();
        for item in &items.items {
            match item {
                &ItemId::Function(func_id) => {
                    let func = &items[func_id];
                    let body = lower_function_body(func.ast.to_node(file.syntax()));
                    let _result = infer(&mut analysis, &items, func, &body);
                    out.push_str(&print_function(func, &body));
                    out.push('\n');
                }
                ItemId::Record(_structure) => {}
                ItemId::Const(_) => todo!(),
                ItemId::Enum(_) => todo!(),
            }
        }
        expected.assert_eq(&out);
    }

    #[test]
    fn test_misc() {
        check(
            "
struct Vec2 {
    x i32
    y i32
}
fn get_x(v Vec2) { return v.x }
fn exit(n i32)
fn do_exit() { exit(0) }
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}
fn double(x i32) { return x + x }
fn square(x i32) { return x * x }
fn negate(x i32) { return -x }
fn complement(x i32) { return !x }
fn bitand(x i32, y i32) { return x & y }
fn bitor(x i32, y i32) { return x | y }
fn bitxor(x i32, y i32) { return x ^ y }
",
            expect![[r#"
                fn get_x(Vec2) unit {
                    return v.x
                }
                fn exit(i32) unit <missing>
                fn do_exit() unit {
                    exit(0)
                }
                fn fib(u32) u32 {
                    if n <= 1 {
                        return 1
                    }
                    return fib(n - 1) + fib(n - 2)
                }
                fn double(i32) unit {
                    return x + x
                }
                fn square(i32) unit {
                    return x * x
                }
                fn negate(i32) unit {
                    return -x
                }
                fn complement(i32) unit {
                    return !x
                }
                fn bitand(i32, i32) unit {
                    return x & y
                }
                fn bitor(i32, i32) unit {
                    return x | y
                }
                fn bitxor(i32, i32) unit {
                    return x ^ y
                }
            "#]],
        );
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
        Type::Record(record) => write!(s, "record {record:?}").unwrap(),
        Type::GenericFn { ret_ty: _, param_tys: _ } => s.push_str("Type::GenericFn"),
        Type::SpecificFn {
            name: _,
            ret_ty: _,
            param_tys: _,
        } => s.push_str("Type::SpecificFn"),
        Type::Enum(_enum_id) => todo!(),
        Type::Unresolved(idx) => write!(s, "unresolved {}", idx.into_raw()).unwrap(),
    }
}
