use crate::{ast::*, AstChildren, AstNode, Language, Syntax, SyntaxNode, SyntaxToken};
use rowan::ast::support::{child, children, token};
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct File {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for File {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::File
    }
    fn cast(node: SyntaxNode) -> Option<File> {
        if File::can_cast(node.kind()) { Some(File { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemStmt {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ItemStmt {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ItemStmt
    }
    fn cast(node: SyntaxNode) -> Option<ItemStmt> {
        if ItemStmt::can_cast(node.kind()) { Some(ItemStmt { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExprStmt {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ExprStmt {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ExprStmt
    }
    fn cast(node: SyntaxNode) -> Option<ExprStmt> {
        if ExprStmt::can_cast(node.kind()) { Some(ExprStmt { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LetStmt {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for LetStmt {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::LetStmt
    }
    fn cast(node: SyntaxNode) -> Option<LetStmt> {
        if LetStmt::can_cast(node.kind()) { Some(LetStmt { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for FnItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::FnItem
    }
    fn cast(node: SyntaxNode) -> Option<FnItem> {
        if FnItem::can_cast(node.kind()) { Some(FnItem { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for EnumItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::EnumItem
    }
    fn cast(node: SyntaxNode) -> Option<EnumItem> {
        if EnumItem::can_cast(node.kind()) { Some(EnumItem { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnionItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for UnionItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::UnionItem
    }
    fn cast(node: SyntaxNode) -> Option<UnionItem> {
        if UnionItem::can_cast(node.kind()) { Some(UnionItem { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for StructItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::StructItem
    }
    fn cast(node: SyntaxNode) -> Option<StructItem> {
        if StructItem::can_cast(node.kind()) { Some(StructItem { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for VariantItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::VariantItem
    }
    fn cast(node: SyntaxNode) -> Option<VariantItem> {
        if VariantItem::can_cast(node.kind()) {
            Some(VariantItem { node })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstItem {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ConstItem {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ConstItem
    }
    fn cast(node: SyntaxNode) -> Option<ConstItem> {
        if ConstItem::can_cast(node.kind()) { Some(ConstItem { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Parameter {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for Parameter {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::Parameter
    }
    fn cast(node: SyntaxNode) -> Option<Parameter> {
        if Parameter::can_cast(node.kind()) { Some(Parameter { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BlockExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for BlockExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::BlockExpr
    }
    fn cast(node: SyntaxNode) -> Option<BlockExpr> {
        if BlockExpr::can_cast(node.kind()) { Some(BlockExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variant {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for Variant {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::Variant
    }
    fn cast(node: SyntaxNode) -> Option<Variant> {
        if Variant::can_cast(node.kind()) { Some(Variant { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Member {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for Member {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::Member
    }
    fn cast(node: SyntaxNode) -> Option<Member> {
        if Member::can_cast(node.kind()) { Some(Member { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ParenExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ParenExpr
    }
    fn cast(node: SyntaxNode) -> Option<ParenExpr> {
        if ParenExpr::can_cast(node.kind()) { Some(ParenExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NameExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for NameExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::NameExpr
    }
    fn cast(node: SyntaxNode) -> Option<NameExpr> {
        if NameExpr::can_cast(node.kind()) { Some(NameExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for LiteralExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::LiteralExpr
    }
    fn cast(node: SyntaxNode) -> Option<LiteralExpr> {
        if LiteralExpr::can_cast(node.kind()) {
            Some(LiteralExpr { node })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for IfExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::IfExpr
    }
    fn cast(node: SyntaxNode) -> Option<IfExpr> {
        if IfExpr::can_cast(node.kind()) { Some(IfExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LoopExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for LoopExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::LoopExpr
    }
    fn cast(node: SyntaxNode) -> Option<LoopExpr> {
        if LoopExpr::can_cast(node.kind()) { Some(LoopExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WhileExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for WhileExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::WhileExpr
    }
    fn cast(node: SyntaxNode) -> Option<WhileExpr> {
        if WhileExpr::can_cast(node.kind()) { Some(WhileExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnaryExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for UnaryExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::UnaryExpr
    }
    fn cast(node: SyntaxNode) -> Option<UnaryExpr> {
        if UnaryExpr::can_cast(node.kind()) { Some(UnaryExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinaryExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for BinaryExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::BinaryExpr
    }
    fn cast(node: SyntaxNode) -> Option<BinaryExpr> {
        if BinaryExpr::can_cast(node.kind()) { Some(BinaryExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BreakExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for BreakExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::BreakExpr
    }
    fn cast(node: SyntaxNode) -> Option<BreakExpr> {
        if BreakExpr::can_cast(node.kind()) { Some(BreakExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReturnExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ReturnExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ReturnExpr
    }
    fn cast(node: SyntaxNode) -> Option<ReturnExpr> {
        if ReturnExpr::can_cast(node.kind()) { Some(ReturnExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ContinueExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ContinueExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ContinueExpr
    }
    fn cast(node: SyntaxNode) -> Option<ContinueExpr> {
        if ContinueExpr::can_cast(node.kind()) {
            Some(ContinueExpr { node })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for CallExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::CallExpr
    }
    fn cast(node: SyntaxNode) -> Option<CallExpr> {
        if CallExpr::can_cast(node.kind()) { Some(CallExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for IndexExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::IndexExpr
    }
    fn cast(node: SyntaxNode) -> Option<IndexExpr> {
        if IndexExpr::can_cast(node.kind()) { Some(IndexExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldExpr {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for FieldExpr {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::FieldExpr
    }
    fn cast(node: SyntaxNode) -> Option<FieldExpr> {
        if FieldExpr::can_cast(node.kind()) { Some(FieldExpr { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Argument {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for Argument {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::Argument
    }
    fn cast(node: SyntaxNode) -> Option<Argument> {
        if Argument::can_cast(node.kind()) { Some(Argument { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenType {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for ParenType {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::ParenType
    }
    fn cast(node: SyntaxNode) -> Option<ParenType> {
        if ParenType::can_cast(node.kind()) { Some(ParenType { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NameType {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for NameType {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::NameType
    }
    fn cast(node: SyntaxNode) -> Option<NameType> {
        if NameType::can_cast(node.kind()) { Some(NameType { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SliceType {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for SliceType {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::SliceType
    }
    fn cast(node: SyntaxNode) -> Option<SliceType> {
        if SliceType::can_cast(node.kind()) { Some(SliceType { node }) } else { None }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PointerType {
    pub(super) node: SyntaxNode,
}
#[rustfmt::skip]
impl AstNode for PointerType {
    type Language = Language;
    fn can_cast(kind: Syntax) -> bool {
        kind == Syntax::PointerType
    }
    fn cast(node: SyntaxNode) -> Option<PointerType> {
        if PointerType::can_cast(node.kind()) {
            Some(PointerType { node })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.node
    }
}
#[rustfmt::skip]
impl File {
    pub fn items(&self) -> AstChildren<Item> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl ItemStmt {
    pub fn item(&self) -> Option<Item> {
        child(&self.node)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
}
#[rustfmt::skip]
impl ExprStmt {
    pub fn expr(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
}
#[rustfmt::skip]
impl LetStmt {
    pub fn ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn expr(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn let_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LetKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Colon)
    }
    pub fn equals_sign_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::EqualsSign)
    }
}
#[rustfmt::skip]
impl FnItem {
    pub fn return_ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn body(&self) -> Option<BlockExpr> {
        child(&self.node)
    }
    pub fn fn_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::FnKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn left_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftParenthesis)
    }
    pub fn right_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightParenthesis)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
    pub fn parameters(&self) -> AstChildren<Parameter> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl EnumItem {
    pub fn enum_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::EnumKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn variants(&self) -> AstChildren<Variant> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl UnionItem {
    pub fn union_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::UnionKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn members(&self) -> AstChildren<Member> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl StructItem {
    pub fn struct_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::StructKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn members(&self) -> AstChildren<Member> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl VariantItem {
    pub fn variant_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::VariantKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn members(&self) -> AstChildren<Member> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl ConstItem {
    pub fn ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn expr(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn const_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::ConstKeyword)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Colon)
    }
    pub fn equals_sign_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::EqualsSign)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
}
#[rustfmt::skip]
impl Parameter {
    pub fn ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Comma)
    }
    pub fn newline_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Newline)
    }
}
#[rustfmt::skip]
impl BlockExpr {
    pub fn left_curly_bracket_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftCurlyBracket)
    }
    pub fn right_curly_bracket_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightCurlyBracket)
    }
    pub fn stmts(&self) -> AstChildren<Stmt> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl Variant {
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
    pub fn newline_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Newline)
    }
}
#[rustfmt::skip]
impl Member {
    pub fn ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Semicolon)
    }
    pub fn newline_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Newline)
    }
}
#[rustfmt::skip]
impl ParenExpr {
    pub fn inner(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn left_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftParenthesis)
    }
    pub fn right_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightParenthesis)
    }
}
#[rustfmt::skip]
impl NameExpr {
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
}
#[rustfmt::skip]
impl LiteralExpr {
    pub fn number_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Number)
    }
    pub fn character_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Character)
    }
    pub fn string_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::String)
    }
}
#[rustfmt::skip]
impl IfExpr {
    pub fn if_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::IfKeyword)
    }
    pub fn else_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::ElseKeyword)
    }
}
#[rustfmt::skip]
impl LoopExpr {
    pub fn body(&self) -> Option<BlockExpr> {
        child(&self.node)
    }
    pub fn loop_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LoopKeyword)
    }
}
#[rustfmt::skip]
impl WhileExpr {
    pub fn condition(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn body(&self) -> Option<BlockExpr> {
        child(&self.node)
    }
    pub fn while_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::WhileKeyword)
    }
}
#[rustfmt::skip]
impl UnaryExpr {
    pub fn operand(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn exclamation_mark_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::ExclamationMark)
    }
    pub fn hyphen_minus_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::HyphenMinus)
    }
    pub fn ref_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RefKeyword)
    }
    pub fn deref_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::DerefKeyword)
    }
}
#[rustfmt::skip]
impl BinaryExpr {}
#[rustfmt::skip]
impl BreakExpr {
    pub fn value(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn break_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::BreakKeyword)
    }
}
#[rustfmt::skip]
impl ReturnExpr {
    pub fn value(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn return_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::ReturnKeyword)
    }
}
#[rustfmt::skip]
impl ContinueExpr {
    pub fn value(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn continue_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::ContinueKeyword)
    }
}
#[rustfmt::skip]
impl CallExpr {
    pub fn callee(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn left_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftParenthesis)
    }
    pub fn right_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightParenthesis)
    }
    pub fn arguments(&self) -> AstChildren<Argument> {
        children(&self.node)
    }
}
#[rustfmt::skip]
impl IndexExpr {
    pub fn left_square_bracket_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftSquareBracket)
    }
    pub fn right_square_bracket_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightSquareBracket)
    }
}
#[rustfmt::skip]
impl FieldExpr {
    pub fn base(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn full_stop_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::FullStop)
    }
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
}
#[rustfmt::skip]
impl Argument {
    pub fn expr(&self) -> Option<Expr> {
        child(&self.node)
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Comma)
    }
    pub fn newline_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Newline)
    }
}
#[rustfmt::skip]
impl ParenType {
    pub fn ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn left_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::LeftParenthesis)
    }
    pub fn right_parenthesis_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::RightParenthesis)
    }
}
#[rustfmt::skip]
impl NameType {
    pub fn identifier_token(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::Identifier)
    }
}
#[rustfmt::skip]
impl SliceType {
    pub fn elem_ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn slice_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::SliceKeyword)
    }
}
#[rustfmt::skip]
impl PointerType {
    pub fn dest_ty(&self) -> Option<Type> {
        child(&self.node)
    }
    pub fn ptr_keyword(&self) -> Option<SyntaxToken> {
        token(&self.node, Syntax::PtrKeyword)
    }
}
