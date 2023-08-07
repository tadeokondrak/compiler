#![warn(unreachable_pub)]

// <generated>
#[macro_export]
#[rustfmt::skip]
macro_rules! t {
    ("eof") => {
        $crate ::Syntax::Eof
    };
    ("error") => {
        $crate ::Syntax::Error
    };
    ("comment") => {
        $crate ::Syntax::Comment
    };
    ("space") => {
        $crate ::Syntax::Space
    };
    ("newline") => {
        $crate ::Syntax::Newline
    };
    ("number") => {
        $crate ::Syntax::Number
    };
    ("string") => {
        $crate ::Syntax::String
    };
    ("character") => {
        $crate ::Syntax::Character
    };
    ("identifier") => {
        $crate ::Syntax::Identifier
    };
    ("!") => {
        $crate ::Syntax::ExclamationMark
    };
    ("!=") => {
        $crate ::Syntax::ExclamationMarkEqualsSign
    };
    ("#") => {
        $crate ::Syntax::NumberSign
    };
    ("$") => {
        $crate ::Syntax::DollarSign
    };
    ("%") => {
        $crate ::Syntax::PercentSign
    };
    ("%=") => {
        $crate ::Syntax::PercentSignEqualsSign
    };
    ("&") => {
        $crate ::Syntax::Ampersand
    };
    ("&=") => {
        $crate ::Syntax::AmpersandEqualsSign
    };
    ("(") => {
        $crate ::Syntax::LeftParenthesis
    };
    (")") => {
        $crate ::Syntax::RightParenthesis
    };
    ("*") => {
        $crate ::Syntax::Asterisk
    };
    ("*=") => {
        $crate ::Syntax::AsteriskEqualsSign
    };
    ("+") => {
        $crate ::Syntax::PlusSign
    };
    ("+=") => {
        $crate ::Syntax::PlusSignEqualsSign
    };
    (",") => {
        $crate ::Syntax::Comma
    };
    ("-") => {
        $crate ::Syntax::HyphenMinus
    };
    ("-=") => {
        $crate ::Syntax::HyphenMinusEqualsSign
    };
    (".") => {
        $crate ::Syntax::FullStop
    };
    ("/") => {
        $crate ::Syntax::Solidus
    };
    ("/=") => {
        $crate ::Syntax::SolidusEqualsSign
    };
    (":") => {
        $crate ::Syntax::Colon
    };
    (";") => {
        $crate ::Syntax::Semicolon
    };
    ("<") => {
        $crate ::Syntax::LessThanSign
    };
    ("<<") => {
        $crate ::Syntax::LessThanSignLessThanSign
    };
    ("<<=") => {
        $crate ::Syntax::LessThanSignLessThanSignEqualsSign
    };
    ("<=") => {
        $crate ::Syntax::LessThanSignEqualsSign
    };
    ("=") => {
        $crate ::Syntax::EqualsSign
    };
    ("==") => {
        $crate ::Syntax::EqualsSignEqualsSign
    };
    (">") => {
        $crate ::Syntax::GreaterThanSign
    };
    (">=") => {
        $crate ::Syntax::GreaterThanSignEqualsSign
    };
    (">>") => {
        $crate ::Syntax::GreaterThanSignGreaterThanSign
    };
    (">>=") => {
        $crate ::Syntax::GreaterThanSignGreaterThanSignEqualsSign
    };
    ("?") => {
        $crate ::Syntax::QuestionMark
    };
    ("@") => {
        $crate ::Syntax::CommercialAt
    };
    ("[") => {
        $crate ::Syntax::LeftSquareBracket
    };
    ("\\") => {
        $crate ::Syntax::ReverseSolidus
    };
    ("]") => {
        $crate ::Syntax::RightSquareBracket
    };
    ("^") => {
        $crate ::Syntax::CircumflexAccent
    };
    ("^=") => {
        $crate ::Syntax::CircumflexAccentEqualsSign
    };
    ("_") => {
        $crate ::Syntax::LowLine
    };
    ("{") => {
        $crate ::Syntax::LeftCurlyBracket
    };
    ("|") => {
        $crate ::Syntax::VerticalLine
    };
    ("|=") => {
        $crate ::Syntax::VerticalLineEqualsSign
    };
    ("}") => {
        $crate ::Syntax::RightCurlyBracket
    };
    ("~") => {
        $crate ::Syntax::Tilde
    };
    ("and") => {
        $crate ::Syntax::AndKeyword
    };
    ("break") => {
        $crate ::Syntax::BreakKeyword
    };
    ("const") => {
        $crate ::Syntax::ConstKeyword
    };
    ("continue") => {
        $crate ::Syntax::ContinueKeyword
    };
    ("deref") => {
        $crate ::Syntax::DerefKeyword
    };
    ("else") => {
        $crate ::Syntax::ElseKeyword
    };
    ("enum") => {
        $crate ::Syntax::EnumKeyword
    };
    ("fn") => {
        $crate ::Syntax::FnKeyword
    };
    ("if") => {
        $crate ::Syntax::IfKeyword
    };
    ("let") => {
        $crate ::Syntax::LetKeyword
    };
    ("loop") => {
        $crate ::Syntax::LoopKeyword
    };
    ("or") => {
        $crate ::Syntax::OrKeyword
    };
    ("ptr") => {
        $crate ::Syntax::PtrKeyword
    };
    ("ref") => {
        $crate ::Syntax::RefKeyword
    };
    ("return") => {
        $crate ::Syntax::ReturnKeyword
    };
    ("slice") => {
        $crate ::Syntax::SliceKeyword
    };
    ("struct") => {
        $crate ::Syntax::StructKeyword
    };
    ("union") => {
        $crate ::Syntax::UnionKeyword
    };
    ("variant") => {
        $crate ::Syntax::VariantKeyword
    };
    ("while") => {
        $crate ::Syntax::WhileKeyword
    };
}
// </generated>

#[cfg(test)]
mod codegen;
mod grammar;
mod lexer;
mod parser;

mod generated {
    pub(crate) mod ast_enums;
    pub(crate) mod ast_nodes;
    pub(crate) mod syntax;
}

pub mod ast {
    pub use super::generated::{ast_enums::*, ast_nodes::*};
    use crate::{ArithOp, BinaryOp, CmpOp, LogicOp, SyntaxToken, UnaryOp};
    use rowan::{ast::AstNode, NodeOrToken};

    impl BinaryExpr {
        pub fn lhs(&self) -> Option<Expr> {
            self.syntax().children().filter_map(Expr::cast).next()
        }

        pub fn rhs(&self) -> Option<Expr> {
            self.syntax()
                .children()
                .filter_map(Expr::cast)
                .skip(1)
                .next()
        }
    }

    impl IfExpr {
        pub fn condition(&self) -> Option<Expr> {
            let exprs = &mut self.syntax().children().filter_map(Expr::cast);
            match exprs.next() {
                first @ Some(Expr::BlockExpr(_)) => exprs.next().and(first),
                first => first,
            }
        }

        pub fn then_body(&self) -> Option<BlockExpr> {
            match self.syntax().children().filter_map(Expr::cast).nth(1)? {
                Expr::BlockExpr(it) => Some(it),
                _ => None,
            }
        }

        pub fn else_body(&self) -> Option<BlockExpr> {
            match self.syntax().children().filter_map(Expr::cast).nth(2)? {
                Expr::BlockExpr(it) => Some(it),
                _ => None,
            }
        }
    }

    impl IndexExpr {
        pub fn base(&self) -> Option<Expr> {
            self.syntax().children().filter_map(Expr::cast).next()
        }

        pub fn index(&self) -> Option<Expr> {
            self.syntax()
                .children()
                .filter_map(Expr::cast)
                .skip(1)
                .next()
        }
    }

    impl UnaryExpr {
        pub fn op_token(&self) -> Option<SyntaxToken> {
            self.syntax()
                .children_with_tokens()
                .filter(|it| !it.kind().is_trivia())
                .find_map(NodeOrToken::into_token)
        }

        pub fn op(&self) -> UnaryOp {
            match self.op_token().unwrap().kind() {
                t!("!") => UnaryOp::Not,
                t!("-") => UnaryOp::Neg,
                t!("ref") => UnaryOp::Ref,
                t!("deref") => UnaryOp::Deref,
                _ => unreachable!(),
            }
        }
    }

    impl BinaryExpr {
        pub fn op_token(&self) -> Option<SyntaxToken> {
            self.syntax()
                .children_with_tokens()
                .filter(|it| !it.kind().is_trivia())
                .find_map(NodeOrToken::into_token)
        }

        pub fn op(&self) -> BinaryOp {
            match self.op_token().unwrap().kind() {
                t!("+") => BinaryOp::Arith(ArithOp::Add),
                t!("-") => BinaryOp::Arith(ArithOp::Sub),
                t!("*") => BinaryOp::Arith(ArithOp::Mul),
                t!("/") => BinaryOp::Arith(ArithOp::Div),
                t!("%") => BinaryOp::Arith(ArithOp::Rem),
                t!("&") => BinaryOp::Arith(ArithOp::And),
                t!("|") => BinaryOp::Arith(ArithOp::Or),
                t!("^") => BinaryOp::Arith(ArithOp::Xor),
                t!("<<") => BinaryOp::Arith(ArithOp::Shl),
                t!(">>") => BinaryOp::Arith(ArithOp::Shr),
                t!("+=") => BinaryOp::Asg(Some(ArithOp::Add)),
                t!("-=") => BinaryOp::Asg(Some(ArithOp::Sub)),
                t!("*=") => BinaryOp::Asg(Some(ArithOp::Mul)),
                t!("/=") => BinaryOp::Asg(Some(ArithOp::Div)),
                t!("%=") => BinaryOp::Asg(Some(ArithOp::Rem)),
                t!("&=") => BinaryOp::Asg(Some(ArithOp::And)),
                t!("|=") => BinaryOp::Asg(Some(ArithOp::Or)),
                t!("^=") => BinaryOp::Asg(Some(ArithOp::Xor)),
                t!("<<=") => BinaryOp::Asg(Some(ArithOp::Shl)),
                t!(">>=") => BinaryOp::Asg(Some(ArithOp::Shr)),
                t!("=") => BinaryOp::Asg(None),
                t!("<") => BinaryOp::Cmp(CmpOp::Lt),
                t!(">") => BinaryOp::Cmp(CmpOp::Gt),
                t!("==") => BinaryOp::Cmp(CmpOp::Eq),
                t!("!=") => BinaryOp::Cmp(CmpOp::Ne),
                t!("<=") => BinaryOp::Cmp(CmpOp::Lte),
                t!(">=") => BinaryOp::Cmp(CmpOp::Gte),
                t!("and") => BinaryOp::Logic(LogicOp::And),
                t!("or") => BinaryOp::Logic(LogicOp::Or),
                t => unreachable!("{t:?}"),
            }
        }
    }
}

pub use generated::syntax::Syntax;

#[repr(i8)]
#[derive(Debug, Clone, Copy)]
enum Assoc {
    Left = -1,
    None = 0,
    Right = 1,
}

#[derive(Debug, Clone, Copy)]
#[repr(i8)]
enum ExprPrec {
    Zero = 0,
    Asg = 2,
    LogicOr = 4,
    LogicAnd = 6,
    Cmp = 8,
    BitOr = 10,
    BitXor = 12,
    BitAnd = 14,
    ShlShr = 16,
    AddSub = 18,
    MulDivRem = 20,
    NotNegRefDeref = 22,
    CallIndexMember = 24,
}

#[derive(Debug, Clone, Copy)]
#[repr(i8)]
enum TypePrec {
    Zero = 0,
    PtrSlice = 10,
}

impl Syntax {
    fn type_prefix_prec(self) -> Option<TypePrec> {
        match self {
            t!("ptr") | t!("slice") => Some(TypePrec::PtrSlice),
            _ => None,
        }
    }

    fn expr_prefix_prec(self) -> Option<ExprPrec> {
        match self {
            t!("!") | t!("-") | t!("ref") | t!("deref") => Some(ExprPrec::NotNegRefDeref),
            _ => None,
        }
    }

    #[rustfmt::skip]
    fn expr_infix_prec_assoc(self) -> Option<(ExprPrec, Assoc)> {
        match self {
            t!("=")
            | t!("-=") | t!("*=") | t!("/=") | t!("&=") | t!("%=")
            | t!("^=") | t!("+=") | t!("<<=") | t!(">>=") | t!("|=") => {
                Some((ExprPrec::Asg, Assoc::Right))
            }
            t!("or") => {
                Some((ExprPrec::LogicOr, Assoc::Left))
            }
            t!("and") => {
                Some((ExprPrec::LogicAnd, Assoc::Left))
            }
            t!("!") | t!("!=") | t!("<") | t!("<=") | t!("==") | t!(">") | t!(">=") => {
                Some((ExprPrec::Cmp, Assoc::None))
            }
            t!("|") => {
                Some((ExprPrec::BitOr, Assoc::Left))
            }
            t!("^") => {
                Some((ExprPrec::BitXor, Assoc::Left))
            }
            t!("&") => {
                Some((ExprPrec::BitAnd, Assoc::Left))
            }
            t!("<<") | t!(">>") => {
                Some((ExprPrec::ShlShr, Assoc::Left))
            }
            t!("+") | t!("-") => {
                Some((ExprPrec::AddSub, Assoc::Left))
            }
            t!("*") | t!("/") | t!("%") => {
                Some((ExprPrec::MulDivRem, Assoc::Left))
            }
            _ => None,
        }
    }

    fn expr_postfix_prec(self) -> Option<ExprPrec> {
        match self {
            t!(".") | t!("(") | t!("[") => Some(ExprPrec::CallIndexMember),
            _ => None,
        }
    }

    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            Syntax::Error | Syntax::Space | Syntax::Newline | Syntax::Comment
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Language;

impl rowan::Language for Language {
    type Kind = Syntax;

    fn kind_from_raw(rowan::SyntaxKind(raw): rowan::SyntaxKind) -> Syntax {
        assert!(raw <= Syntax::LAST as u16);
        unsafe { std::mem::transmute(raw) }
    }

    fn kind_to_raw(kind: Syntax) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

pub type SyntaxNode = rowan::api::SyntaxNode<Language>;
pub type SyntaxNodeChildren = rowan::api::SyntaxNodeChildren<Language>;
pub type SyntaxToken = rowan::api::SyntaxToken<Language>;
pub type SyntaxElement = rowan::api::SyntaxElement<Language>;
pub type SyntaxElementChildren = rowan::api::SyntaxElementChildren<Language>;
pub type Preorder = rowan::api::Preorder<Language>;
pub type PreorderWithTokens = rowan::api::PreorderWithTokens<Language>;
pub use rowan::ast::{AstChildren, AstNode, AstPtr, SyntaxNodePtr};
pub use rowan::NodeOrToken;

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Not,
    Neg,
    Ref,
    Deref,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Asg(Option<ArithOp>),
    Cmp(CmpOp),
    Arith(ArithOp),
    Logic(LogicOp),
}

#[derive(Debug, Clone, Copy)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Lte,
    Gt,
    Gte,
}

#[derive(Debug, Clone, Copy)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy)]
pub enum LogicOp {
    And,
    Or,
}

pub fn parse_file(src: &str) -> ast::File {
    let (node, errors) = parser::parse_file(src);
    assert!(errors.is_empty());
    let node = SyntaxNode::new_root(node);
    ast::File::cast(node).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};

    #[test]
    fn test_parse() {
        check(
            "
fn fib(n u32) ptr u32 {
    if n <= 1 {
        return 1
    }
    return fib(n - 1) + fib(n - 2)
}",
            expect![[r#"
                File {
                    node: File@0..100
                      Newline@0..1 "\n"
                      FnItem@1..100
                        FnKeyword@1..3 "fn"
                        Space@3..4 " "
                        Identifier@4..7 "fib"
                        LeftParenthesis@7..8 "("
                        Parameter@8..13
                          Identifier@8..9 "n"
                          Space@9..10 " "
                          NameType@10..13
                            Identifier@10..13 "u32"
                        RightParenthesis@13..14 ")"
                        Space@14..15 " "
                        PointerType@15..22
                          PtrKeyword@15..18 "ptr"
                          Space@18..19 " "
                          NameType@19..22
                            Identifier@19..22 "u32"
                        Space@22..23 " "
                        BlockExpr@23..100
                          LeftCurlyBracket@23..24 "{"
                          Newline@24..25 "\n"
                          Space@25..29 "    "
                          ExprStmt@29..64
                            IfExpr@29..63
                              IfKeyword@29..31 "if"
                              Space@31..32 " "
                              BinaryExpr@32..38
                                NameExpr@32..33
                                  Identifier@32..33 "n"
                                Space@33..34 " "
                                LessThanSignEqualsSign@34..36 "<="
                                Space@36..37 " "
                                LiteralExpr@37..38
                                  Number@37..38 "1"
                              Space@38..39 " "
                              BlockExpr@39..63
                                LeftCurlyBracket@39..40 "{"
                                Newline@40..41 "\n"
                                Space@41..49 "        "
                                ExprStmt@49..57
                                  ReturnExpr@49..57
                                    ReturnKeyword@49..55 "return"
                                    Space@55..56 " "
                                    LiteralExpr@56..57
                                      Number@56..57 "1"
                                Newline@57..58 "\n"
                                Space@58..62 "    "
                                RightCurlyBracket@62..63 "}"
                            Newline@63..64 "\n"
                          Space@64..68 "    "
                          ExprStmt@68..98
                            ReturnExpr@68..98
                              ReturnKeyword@68..74 "return"
                              Space@74..75 " "
                              BinaryExpr@75..98
                                CallExpr@75..85
                                  NameExpr@75..78
                                    Identifier@75..78 "fib"
                                  LeftParenthesis@78..79 "("
                                  Argument@79..84
                                    BinaryExpr@79..84
                                      NameExpr@79..80
                                        Identifier@79..80 "n"
                                      Space@80..81 " "
                                      HyphenMinus@81..82 "-"
                                      Space@82..83 " "
                                      LiteralExpr@83..84
                                        Number@83..84 "1"
                                  RightParenthesis@84..85 ")"
                                Space@85..86 " "
                                PlusSign@86..87 "+"
                                Space@87..88 " "
                                CallExpr@88..98
                                  NameExpr@88..91
                                    Identifier@88..91 "fib"
                                  LeftParenthesis@91..92 "("
                                  Argument@92..97
                                    BinaryExpr@92..97
                                      NameExpr@92..93
                                        Identifier@92..93 "n"
                                      Space@93..94 " "
                                      HyphenMinus@94..95 "-"
                                      Space@95..96 " "
                                      LiteralExpr@96..97
                                        Number@96..97 "2"
                                  RightParenthesis@97..98 ")"
                          Newline@98..99 "\n"
                          RightCurlyBracket@99..100 "}"
                    ,
                }
            "#]],
        );
        check(
            "
struct X {
    field i32;
    other u32;
}",
            expect![[r#"
                File {
                    node: File@0..43
                      Newline@0..1 "\n"
                      StructItem@1..43
                        StructKeyword@1..7 "struct"
                        Space@7..8 " "
                        Identifier@8..9 "X"
                        Space@9..10 " "
                        LeftCurlyBracket@10..11 "{"
                        Newline@11..12 "\n"
                        Space@12..16 "    "
                        Member@16..26
                          Identifier@16..21 "field"
                          Space@21..22 " "
                          NameType@22..25
                            Identifier@22..25 "i32"
                          Semicolon@25..26 ";"
                        Newline@26..27 "\n"
                        Space@27..31 "    "
                        Member@31..41
                          Identifier@31..36 "other"
                          Space@36..37 " "
                          NameType@37..40
                            Identifier@37..40 "u32"
                          Semicolon@40..41 ";"
                        Newline@41..42 "\n"
                        RightCurlyBracket@42..43 "}"
                    ,
                }
            "#]],
        );
    }

    fn check(src: &str, expected: Expect) {
        let file = parse_file(src);
        expected.assert_debug_eq(&file);
    }
}
