use super::{
    SyntaxKind::{self, *},
    SyntaxNode, SyntaxToken,
};
use crate::{Binop, Language, Unop};
use rowan::ast::{support, AstChildren, AstNode};

macro_rules! ast_wrappers {
    () => {};
    (#[kind($p:pat)] pub struct $T:ident {$($fields:tt)*} $($rest:tt)*) => {
        pub struct $T {
            raw: SyntaxNode,
        }
        impl AstNode for $T {
            type Language = Language;

            fn can_cast(kind: SyntaxKind) -> bool {
                matches!(kind, $p)
            }

            fn cast(raw: SyntaxNode) -> Option<Self> {
                Self::can_cast(raw.kind()).then_some(Self { raw })
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.raw
            }
        }
        impl $T {
            ast_wrappers!(@fields $($fields)*);
        }
        ast_wrappers!($($rest)*);
    };
    (@fields) => {};
    (@fields #[kind($field_kind:expr)] pub fn $field:ident(&self) -> Option<SyntaxToken>; $($rest:tt)*) => {
        pub fn $field(&self) -> Option<SyntaxToken> {
            support::token(self.syntax(), $field_kind)
        }
        ast_wrappers!(@fields $($rest)*);
    };
    (@fields pub fn $field:ident(&self) -> Option<$Ret:ty>; $($rest:tt)*) => {
        pub fn $field(&self) -> Option<$Ret> {
            support::child(self.syntax())
        }
        ast_wrappers!(@fields $($rest)*);
    };
    (@fields pub fn $field:ident(&self) -> AstChildren<$N:ty>; $($rest:tt)*) => {
        pub fn $field(&self) -> AstChildren<$N> {
            support::children::<$N>(self.syntax())
        }
        ast_wrappers!(@fields $($rest)*);
    };

}

macro_rules! ast_enums {
    () => {};
    (pub enum $T:ident $(: $($imp:ident)+*)? { $(#[kind($p:pat)] $Variant:ident($Wrapper:ident),)* } $($rest:tt)*) => {
        pub enum $T {
            $($Variant($Wrapper),)*
        }
        impl AstNode for $T {
            type Language = Language;
            fn can_cast(kind: SyntaxKind) -> bool {
                matches!(kind, $($p)|*)
            }
            fn cast(raw: SyntaxNode) -> Option<Self> {
                match raw.kind() {
                    $($p => $Wrapper::cast(raw).map(Self::$Variant),)*
                    _ => None,
                }
            }
            fn syntax(&self) -> &SyntaxNode {
                match self {
                    $(Self::$Variant(it) => it.syntax(),)*
                }
            }
        }
        ast_enums!($($rest)*);
    };
}

ast_wrappers! {
    #[kind(ROOT)]
    pub struct Root {
        pub fn items(&self) -> AstChildren<Item>;
    }

    #[kind(IDENT_TYPE)]
    pub struct IdentType {
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
    }

    #[kind(SLICE_TYPE)]
    pub struct SliceType {
        #[kind(LEFT_BRACKET)]
        pub fn left_bracket(&self) -> Option<SyntaxToken>;
        #[kind(RIGHT_BRACKET)]
        pub fn right_bracket(&self) -> Option<SyntaxToken>;
        pub fn element(&self) -> Option<Type>;
    }

    #[kind(PARAM)]
    pub struct Param {
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
        pub fn ty(&self) -> Option<Type>;
    }

    #[kind(PARAM_LIST)]
    pub struct ParamList {
        pub fn params(&self) -> AstChildren<Param>;
    }

    #[kind(FN_ITEM)]
    pub struct FnItem {
        #[kind(FN_KW)]
        pub fn fn_token(&self) -> Option<SyntaxToken>;
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
        pub fn param_list(&self) -> Option<ParamList>;
        pub fn return_ty(&self) -> Option<Type>;
        pub fn body(&self) -> Option<BlockExpr>;
    }

    #[kind(CONST_ITEM)]
    pub struct ConstItem {
        #[kind(CONST_KW)]
        pub fn const_token(&self) -> Option<SyntaxToken>;
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
        pub fn value(&self) -> Option<Expr>;
    }

    #[kind(STATIC_ITEM)]
    pub struct StaticItem {
        #[kind(STATIC_KW)]
        pub fn static_token(&self) -> Option<SyntaxToken>;
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
        pub fn value(&self) -> Option<Expr>;
    }

    #[kind(CONTAINER_ITEM)]
    pub struct ContainerItem {
        #[kind(STRUCT_KW)]
        pub fn struct_token(&self) -> Option<SyntaxToken>;
        #[kind(ENUM_KW)]
        pub fn enum_token(&self) -> Option<SyntaxToken>;
        #[kind(UNION_KW)]
        pub fn union_token(&self) -> Option<SyntaxToken>;
        #[kind(EXTERN_KW)]
        pub fn extern_token(&self) -> Option<SyntaxToken>;
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
    }

    #[kind(BLOCK_EXPR)]
    pub struct BlockExpr {
        #[kind(LEFT_BRACKET)]
        pub fn left_bracket(&self) -> Option<SyntaxToken>;
        #[kind(RIGHT_BRACKET)]
        pub fn right_bracket(&self) -> Option<SyntaxToken>;
        pub fn stmts(&self) -> AstChildren<Stmt>;
    }

    #[kind(LITERAL_EXPR)]
    pub struct LiteralExpr {
        #[kind(INTEGER)]
        pub fn integer_token(&self) -> Option<SyntaxToken>;
        #[kind(CHARACTER)]
        pub fn character_token(&self) -> Option<SyntaxToken>;
        #[kind(STRING)]
        pub fn string_token(&self) -> Option<SyntaxToken>;
    }

    #[kind(IDENT_EXPR)]
    pub struct IdentExpr {
        #[kind(IDENT)]
        pub fn ident(&self) -> Option<SyntaxToken>;
    }

    #[kind(UNARY_EXPR)]
    pub struct UnaryExpr {}

    #[kind(BINARY_EXPR)]
    pub struct BinaryExpr {}

    #[kind(RETURN_EXPR)]
    pub struct ReturnExpr {
        #[kind(RETURN_KW)]
        pub fn return_token(&self) -> Option<SyntaxToken>;
        pub fn expr(&self) -> Option<Expr>;
    }

    #[kind(LET_STMT)]
    pub struct LetStmt {
        #[kind(LET_KW)]
        pub fn let_token(&self) -> Option<SyntaxToken>;
        #[kind(IDENT_TYPE)]
        pub fn ident(&self) -> Option<SyntaxToken>;
    }
}

ast_enums! {
    pub enum Item {
        #[kind(FN_ITEM)]
        Fn(FnItem),
        #[kind(CONST_ITEM)]
        Const(ConstItem),
        #[kind(STATIC_ITEM)]
        Static(StaticItem),
        #[kind(CONTAINER_ITEM)]
        Container(ContainerItem),
    }

    pub enum Expr {
        #[kind(LITERAL_EXPR)]
        Literal(LiteralExpr),
        #[kind(IDENT_EXPR)]
        Ident(IdentExpr),
        #[kind(BLOCK_EXPR)]
        Block(BlockExpr),
        #[kind(UNARY_EXPR)]
        Unary(UnaryExpr),
        #[kind(BINARY_EXPR)]
        Binary(BinaryExpr),
    }

    pub enum Stmt {
        #[kind(LET_STMT)]
        Let(LetStmt),
    }

    pub enum Type {
        #[kind(NAME)]
        Ident(IdentType),
        #[kind(SLICE_TYPE)]
        Slice(SliceType),
    }
}

impl UnaryExpr {
    pub fn operand(&self) -> Option<Expr> {
        support::children(&self.raw).next()
    }

    pub fn operator(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|it| matches!(it.kind(), MINUS | BANG))
    }

    pub fn op(&self) -> Option<Unop> {
        match self.operator()?.kind() {
            MINUS => Some(Unop::Neg),
            BANG => Some(Unop::Not),
            _ => None,
        }
    }
}

impl BinaryExpr {
    pub fn lhs(&self) -> Option<Expr> {
        support::children(&self.raw).next()
    }

    pub fn rhs(&self) -> Option<Expr> {
        support::children(&self.raw).nth(1)
    }

    pub fn operator(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|it| {
                matches!(
                    it.kind(),
                    PLUS | MINUS
                        | STAR
                        | SLASH
                        | PERCENT
                        | LESS2
                        | GREATER2
                        | AMPERSAND
                        | PIPE
                        | CARET
                )
            })
    }

    pub fn op(&self) -> Option<Binop> {
        match self.operator()?.kind() {
            PLUS => Some(Binop::Add),
            MINUS => Some(Binop::Sub),
            STAR => Some(Binop::Mul),
            SLASH => Some(Binop::Div),
            PERCENT => Some(Binop::Rem),
            LESS2 => Some(Binop::Shl),
            GREATER2 => Some(Binop::Shr),
            AMPERSAND => Some(Binop::And),
            PIPE => Some(Binop::Or),
            CARET => Some(Binop::Xor),
            _ => todo!(),
        }
    }
}
