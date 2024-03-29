use crate::{ast::*, AstNode, Language, Syntax, SyntaxNode};
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Item {
    FnItem(FnItem),
    EnumItem(EnumItem),
    RecordItem(RecordItem),
    ConstItem(ConstItem),
}
#[rustfmt::skip]
impl AstNode for Item {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        matches!(
            kind, Syntax::FnItem | Syntax::EnumItem | Syntax::RecordItem |
            Syntax::ConstItem
        )
    }
    fn cast(node: SyntaxNode) -> Option<Item> {
        match node.kind() {
            Syntax::FnItem => Some(Item::FnItem(FnItem { node })),
            Syntax::EnumItem => Some(Item::EnumItem(EnumItem { node })),
            Syntax::RecordItem => Some(Item::RecordItem(RecordItem { node })),
            Syntax::ConstItem => Some(Item::ConstItem(ConstItem { node })),
            _ => None,
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Item::FnItem(FnItem { node }) => node,
            Item::EnumItem(EnumItem { node }) => node,
            Item::RecordItem(RecordItem { node }) => node,
            Item::ConstItem(ConstItem { node }) => node,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    ItemStmt(ItemStmt),
    ExprStmt(ExprStmt),
    LetStmt(LetStmt),
}
#[rustfmt::skip]
impl AstNode for Stmt {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        matches!(kind, Syntax::ItemStmt | Syntax::ExprStmt | Syntax::LetStmt)
    }
    fn cast(node: SyntaxNode) -> Option<Stmt> {
        match node.kind() {
            Syntax::ItemStmt => Some(Stmt::ItemStmt(ItemStmt { node })),
            Syntax::ExprStmt => Some(Stmt::ExprStmt(ExprStmt { node })),
            Syntax::LetStmt => Some(Stmt::LetStmt(LetStmt { node })),
            _ => None,
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Stmt::ItemStmt(ItemStmt { node }) => node,
            Stmt::ExprStmt(ExprStmt { node }) => node,
            Stmt::LetStmt(LetStmt { node }) => node,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    ParenExpr(ParenExpr),
    NameExpr(NameExpr),
    LiteralExpr(LiteralExpr),
    IfExpr(IfExpr),
    LoopExpr(LoopExpr),
    WhileExpr(WhileExpr),
    BlockExpr(BlockExpr),
    UnaryExpr(UnaryExpr),
    BinaryExpr(BinaryExpr),
    BreakExpr(BreakExpr),
    ReturnExpr(ReturnExpr),
    ContinueExpr(ContinueExpr),
    CallExpr(CallExpr),
    IndexExpr(IndexExpr),
    FieldExpr(FieldExpr),
}
#[rustfmt::skip]
impl AstNode for Expr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        matches!(
            kind, Syntax::ParenExpr | Syntax::NameExpr | Syntax::LiteralExpr |
            Syntax::IfExpr | Syntax::LoopExpr | Syntax::WhileExpr | Syntax::BlockExpr |
            Syntax::UnaryExpr | Syntax::BinaryExpr | Syntax::BreakExpr |
            Syntax::ReturnExpr | Syntax::ContinueExpr | Syntax::CallExpr |
            Syntax::IndexExpr | Syntax::FieldExpr
        )
    }
    fn cast(node: SyntaxNode) -> Option<Expr> {
        match node.kind() {
            Syntax::ParenExpr => Some(Expr::ParenExpr(ParenExpr { node })),
            Syntax::NameExpr => Some(Expr::NameExpr(NameExpr { node })),
            Syntax::LiteralExpr => Some(Expr::LiteralExpr(LiteralExpr { node })),
            Syntax::IfExpr => Some(Expr::IfExpr(IfExpr { node })),
            Syntax::LoopExpr => Some(Expr::LoopExpr(LoopExpr { node })),
            Syntax::WhileExpr => Some(Expr::WhileExpr(WhileExpr { node })),
            Syntax::BlockExpr => Some(Expr::BlockExpr(BlockExpr { node })),
            Syntax::UnaryExpr => Some(Expr::UnaryExpr(UnaryExpr { node })),
            Syntax::BinaryExpr => Some(Expr::BinaryExpr(BinaryExpr { node })),
            Syntax::BreakExpr => Some(Expr::BreakExpr(BreakExpr { node })),
            Syntax::ReturnExpr => Some(Expr::ReturnExpr(ReturnExpr { node })),
            Syntax::ContinueExpr => Some(Expr::ContinueExpr(ContinueExpr { node })),
            Syntax::CallExpr => Some(Expr::CallExpr(CallExpr { node })),
            Syntax::IndexExpr => Some(Expr::IndexExpr(IndexExpr { node })),
            Syntax::FieldExpr => Some(Expr::FieldExpr(FieldExpr { node })),
            _ => None,
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Expr::ParenExpr(ParenExpr { node }) => node,
            Expr::NameExpr(NameExpr { node }) => node,
            Expr::LiteralExpr(LiteralExpr { node }) => node,
            Expr::IfExpr(IfExpr { node }) => node,
            Expr::LoopExpr(LoopExpr { node }) => node,
            Expr::WhileExpr(WhileExpr { node }) => node,
            Expr::BlockExpr(BlockExpr { node }) => node,
            Expr::UnaryExpr(UnaryExpr { node }) => node,
            Expr::BinaryExpr(BinaryExpr { node }) => node,
            Expr::BreakExpr(BreakExpr { node }) => node,
            Expr::ReturnExpr(ReturnExpr { node }) => node,
            Expr::ContinueExpr(ContinueExpr { node }) => node,
            Expr::CallExpr(CallExpr { node }) => node,
            Expr::IndexExpr(IndexExpr { node }) => node,
            Expr::FieldExpr(FieldExpr { node }) => node,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    ParenType(ParenType),
    NameType(NameType),
    SliceType(SliceType),
    PointerType(PointerType),
}
#[rustfmt::skip]
impl AstNode for Type {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        matches!(
            kind, Syntax::ParenType | Syntax::NameType | Syntax::SliceType |
            Syntax::PointerType
        )
    }
    fn cast(node: SyntaxNode) -> Option<Type> {
        match node.kind() {
            Syntax::ParenType => Some(Type::ParenType(ParenType { node })),
            Syntax::NameType => Some(Type::NameType(NameType { node })),
            Syntax::SliceType => Some(Type::SliceType(SliceType { node })),
            Syntax::PointerType => Some(Type::PointerType(PointerType { node })),
            _ => None,
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Type::ParenType(ParenType { node }) => node,
            Type::NameType(NameType { node }) => node,
            Type::SliceType(SliceType { node }) => node,
            Type::PointerType(PointerType { node }) => node,
        }
    }
}
