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
use std::fmt;

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
    assert!(errors.is_empty(), "{errors:?}");
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
fn exit(n i32)

fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    exit(0)
    return fib(n - 1) + fib(n - 2)
}",
            expect![[r#"
                File {
                    node: File@0..112
                      Newline@0..1 "\n"
                      FnItem@1..16
                        FnKeyword@1..3 "fn"
                        Space@3..4 " "
                        Identifier@4..8 "exit"
                        LeftParenthesis@8..9 "("
                        Parameter@9..14
                          Identifier@9..10 "n"
                          Space@10..11 " "
                          NameType@11..14
                            Identifier@11..14 "i32"
                        RightParenthesis@14..15 ")"
                        Newline@15..16 "\n"
                      Newline@16..17 "\n"
                      FnItem@17..112
                        FnKeyword@17..19 "fn"
                        Space@19..20 " "
                        Identifier@20..23 "fib"
                        LeftParenthesis@23..24 "("
                        Parameter@24..29
                          Identifier@24..25 "n"
                          Space@25..26 " "
                          NameType@26..29
                            Identifier@26..29 "u32"
                        RightParenthesis@29..30 ")"
                        Space@30..31 " "
                        NameType@31..34
                          Identifier@31..34 "u32"
                        Space@34..35 " "
                        BlockExpr@35..112
                          LeftCurlyBracket@35..36 "{"
                          Newline@36..37 "\n"
                          Space@37..41 "    "
                          ExprStmt@41..64
                            IfExpr@41..63
                              IfKeyword@41..43 "if"
                              Space@43..44 " "
                              BinaryExpr@44..50
                                NameExpr@44..45
                                  Identifier@44..45 "n"
                                Space@45..46 " "
                                LessThanSignEqualsSign@46..48 "<="
                                Space@48..49 " "
                                LiteralExpr@49..50
                                  Number@49..50 "1"
                              Space@50..51 " "
                              BlockExpr@51..63
                                LeftCurlyBracket@51..52 "{"
                                Space@52..53 " "
                                ExprStmt@53..61
                                  ReturnExpr@53..61
                                    ReturnKeyword@53..59 "return"
                                    Space@59..60 " "
                                    LiteralExpr@60..61
                                      Number@60..61 "1"
                                Space@61..62 " "
                                RightCurlyBracket@62..63 "}"
                            Newline@63..64 "\n"
                          Space@64..68 "    "
                          ExprStmt@68..76
                            CallExpr@68..75
                              NameExpr@68..72
                                Identifier@68..72 "exit"
                              LeftParenthesis@72..73 "("
                              Argument@73..74
                                LiteralExpr@73..74
                                  Number@73..74 "0"
                              RightParenthesis@74..75 ")"
                            Newline@75..76 "\n"
                          Space@76..80 "    "
                          ExprStmt@80..110
                            ReturnExpr@80..110
                              ReturnKeyword@80..86 "return"
                              Space@86..87 " "
                              BinaryExpr@87..110
                                CallExpr@87..97
                                  NameExpr@87..90
                                    Identifier@87..90 "fib"
                                  LeftParenthesis@90..91 "("
                                  Argument@91..96
                                    BinaryExpr@91..96
                                      NameExpr@91..92
                                        Identifier@91..92 "n"
                                      Space@92..93 " "
                                      HyphenMinus@93..94 "-"
                                      Space@94..95 " "
                                      LiteralExpr@95..96
                                        Number@95..96 "1"
                                  RightParenthesis@96..97 ")"
                                Space@97..98 " "
                                PlusSign@98..99 "+"
                                Space@99..100 " "
                                CallExpr@100..110
                                  NameExpr@100..103
                                    Identifier@100..103 "fib"
                                  LeftParenthesis@103..104 "("
                                  Argument@104..109
                                    BinaryExpr@104..109
                                      NameExpr@104..105
                                        Identifier@104..105 "n"
                                      Space@105..106 " "
                                      HyphenMinus@106..107 "-"
                                      Space@107..108 " "
                                      LiteralExpr@108..109
                                        Number@108..109 "2"
                                  RightParenthesis@109..110 ")"
                          Newline@110..111 "\n"
                          RightCurlyBracket@111..112 "}"
                    ,
                }
            "#]],
        );
        check(
            "
struct X {
    field i32
    other u32
}",
            expect![[r#"
                File {
                    node: File@0..41
                      Newline@0..1 "\n"
                      RecordItem@1..41
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
                          Newline@25..26 "\n"
                        Space@26..30 "    "
                        Member@30..40
                          Identifier@30..35 "other"
                          Space@35..36 " "
                          NameType@36..39
                            Identifier@36..39 "u32"
                          Newline@39..40 "\n"
                        RightCurlyBracket@40..41 "}"
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


impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Not => f.write_str("!"),
            UnaryOp::Neg => f.write_str("-"),
            UnaryOp::Ref => f.write_str("&"),
            UnaryOp::Deref => f.write_str("*"),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::Asg(None) => f.write_str("="),
            BinaryOp::Asg(Some(op)) => op.fmt(f),
            BinaryOp::Cmp(op) => op.fmt(f),
            BinaryOp::Arith(op) => op.fmt(f),
            BinaryOp::Logic(op) => op.fmt(f),
        }
    }
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CmpOp::Eq => f.write_str("=="),
            CmpOp::Ne => f.write_str("!="),
            CmpOp::Lt => f.write_str("<"),
            CmpOp::Lte => f.write_str("<="),
            CmpOp::Gt => f.write_str(">"),
            CmpOp::Gte => f.write_str(">="),
        }
    }
}
impl fmt::Display for ArithOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithOp::Add => f.write_str("+"),
            ArithOp::Sub => f.write_str("-"),
            ArithOp::Mul => f.write_str("*"),
            ArithOp::Div => f.write_str("/"),
            ArithOp::Rem => f.write_str("%"),
            ArithOp::And => f.write_str("&"),
            ArithOp::Or => f.write_str("|"),
            ArithOp::Xor => f.write_str("^"),
            ArithOp::Shl => f.write_str("<<"),
            ArithOp::Shr => f.write_str(">>"),
        }
    }
}

impl fmt::Display for LogicOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LogicOp::And => f.write_str("and"),
            LogicOp::Or => f.write_str("or"),
        }
    }
}
