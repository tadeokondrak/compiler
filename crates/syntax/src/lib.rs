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
    pub use super::generated::ast_enums::*;
    pub use super::generated::ast_nodes::*;
    use rowan::ast::AstNode;

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
            self.syntax().children().filter_map(Expr::cast).skip(1).next()
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
    Asg = 10,
    Cmp = 20,
    Or = 30,
    Xor = 40,
    And = 50,
    ShlShr = 60,
    AddSub = 70,
    MulDivRem = 80,
    NotNegRefDeref = 90,
    CallIndexMember = 100,
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
            t!("!") | t!("!=") | t!("<") | t!("<=") | t!("==") | t!(">") | t!(">=") => {
                Some((ExprPrec::Cmp, Assoc::None))
            }
            t!("|") => {
                Some((ExprPrec::Or, Assoc::Left))
            }
            t!("^") => {
                Some((ExprPrec::Xor, Assoc::Left))
            }
            t!("&") => {
                Some((ExprPrec::And, Assoc::Left))
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
pub type AstPtr = rowan::ast::AstPtr<Language>;
pub type SyntaxNodePtr = rowan::ast::SyntaxNodePtr<Language>;
pub use rowan::ast::{AstChildren, AstNode};
pub use rowan::NodeOrToken;

pub fn parse_file(src: &str) -> ast::File {
    let (node, errors) = parser::parse_file(src);
    assert!(errors.is_empty());
    let node = SyntaxNode::new_root(node);
    ast::File::cast(node).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn test_parse() {
        let file = parse_file(
            "
            fn fib(n u32) ptr u32 {
                if n <= 1 {
                    return 1
                }
                return fib(n - 1) + fib(n - 2)
            }
        ",
        );
        let expected = expect![[r#"
            File {
                node: File@0..181
                  Newline@0..1 "\n"
                  Space@1..13 "            "
                  FnItem@13..172
                    FnKeyword@13..15 "fn"
                    Space@15..16 " "
                    Identifier@16..19 "fib"
                    LeftParenthesis@19..20 "("
                    Parameter@20..25
                      Identifier@20..21 "n"
                      Space@21..22 " "
                      NameType@22..25
                        Identifier@22..25 "u32"
                    RightParenthesis@25..26 ")"
                    Space@26..27 " "
                    PointerType@27..34
                      PtrKeyword@27..30 "ptr"
                      Space@30..31 " "
                      NameType@31..34
                        Identifier@31..34 "u32"
                    Space@34..35 " "
                    BlockExpr@35..172
                      LeftCurlyBracket@35..36 "{"
                      Newline@36..37 "\n"
                      Space@37..53 "                "
                      ExprStmt@53..112
                        IfExpr@53..111
                          IfKeyword@53..55 "if"
                          Space@55..56 " "
                          BinaryExpr@56..62
                            NameExpr@56..57
                              Identifier@56..57 "n"
                            Space@57..58 " "
                            LessThanSignEqualsSign@58..60 "<="
                            Space@60..61 " "
                            LiteralExpr@61..62
                              Number@61..62 "1"
                          Space@62..63 " "
                          BlockExpr@63..111
                            LeftCurlyBracket@63..64 "{"
                            Newline@64..65 "\n"
                            Space@65..85 "                    "
                            ExprStmt@85..93
                              ReturnExpr@85..93
                                ReturnKeyword@85..91 "return"
                                Space@91..92 " "
                                LiteralExpr@92..93
                                  Number@92..93 "1"
                            Newline@93..94 "\n"
                            Space@94..110 "                "
                            RightCurlyBracket@110..111 "}"
                        Newline@111..112 "\n"
                      Space@112..128 "                "
                      ExprStmt@128..158
                        ReturnExpr@128..158
                          ReturnKeyword@128..134 "return"
                          Space@134..135 " "
                          BinaryExpr@135..158
                            CallExpr@135..145
                              NameExpr@135..138
                                Identifier@135..138 "fib"
                              LeftParenthesis@138..139 "("
                              Argument@139..144
                                BinaryExpr@139..144
                                  NameExpr@139..140
                                    Identifier@139..140 "n"
                                  Space@140..141 " "
                                  HyphenMinus@141..142 "-"
                                  Space@142..143 " "
                                  LiteralExpr@143..144
                                    Number@143..144 "1"
                              RightParenthesis@144..145 ")"
                            Space@145..146 " "
                            PlusSign@146..147 "+"
                            Space@147..148 " "
                            CallExpr@148..158
                              NameExpr@148..151
                                Identifier@148..151 "fib"
                              LeftParenthesis@151..152 "("
                              Argument@152..157
                                BinaryExpr@152..157
                                  NameExpr@152..153
                                    Identifier@152..153 "n"
                                  Space@153..154 " "
                                  HyphenMinus@154..155 "-"
                                  Space@155..156 " "
                                  LiteralExpr@156..157
                                    Number@156..157 "2"
                              RightParenthesis@157..158 ")"
                      Newline@158..159 "\n"
                      Space@159..171 "            "
                      RightCurlyBracket@171..172 "}"
                  Newline@172..173 "\n"
                  Space@173..181 "        "
                ,
            }
        "#]];
        expected.assert_debug_eq(&file);
    }
}
