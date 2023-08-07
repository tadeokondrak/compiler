use super::{grammar, lexer::lex, lexer::Lexeme, Language, Syntax};
use rowan::{GreenNode, GreenNodeBuilder, TextLen, TextRange, TextSize};
use std::cell::Cell;

pub(crate) struct Parser {
    pos: usize,
    tokens: Vec<Syntax>,
    tokens_keyword: Vec<Syntax>,
    tokens_after_trivia: Vec<bool>,
    tokens_after_newline: Vec<bool>,
    events: Vec<Event>,
    fuel: Cell<u8>,
}

#[derive(Debug)]
enum Event {
    Begin { kind: Syntax },
    Token { kind: Syntax, n_input: usize },
    Newline,
    Error { s: Box<str> },
    End,
}

pub(super) fn parse_file(s: &str) -> (GreenNode, Vec<String>) {
    let mut parser = Parser {
        pos: 0,
        tokens: Vec::new(),
        tokens_keyword: Vec::new(),
        tokens_after_trivia: Vec::new(),
        tokens_after_newline: Vec::new(),
        events: Vec::new(),
        fuel: Cell::new(u8::MAX),
    };
    let mut all_tokens = Vec::new();
    let mut all_tokens_text_range = Vec::new();

    let mut pos = TextSize::new(0);
    let mut space_before = false;
    let mut newline_before = false;
    while pos < s.text_len() {
        let (lexeme, len) = lex(&s[usize::from(pos)..]);
        let len = TextSize::try_from(len).expect("token too long");
        let token_text_range = TextRange::at(pos, len);
        let token_text = &s[token_text_range];
        pos += len;
        let token = Syntax::from_lexeme(lexeme, token_text);
        let contextual_token = Syntax::from_keyword_str(token_text).unwrap_or(token);
        all_tokens.push(token);
        all_tokens_text_range.push(token_text_range);
        match lexeme {
            Lexeme::Error | Lexeme::Comment => {
                space_before = true;
                newline_before = false;
            }
            Lexeme::Space => {
                space_before = true;
            }
            Lexeme::Newline => {
                space_before = true;
                newline_before = true;
            }
            Lexeme::Identifier
            | Lexeme::Punctuation
            | Lexeme::NumberLiteral
            | Lexeme::StringLiteral
            | Lexeme::CharacterLiteral => {
                parser.tokens.push(token);
                parser.tokens_keyword.push(contextual_token);
                parser.tokens_after_trivia.push(space_before);
                parser.tokens_after_newline.push(newline_before);
                space_before = false;
                newline_before = false;
            }
        }
    }

    grammar::parse_file(&mut parser);

    let mut token_pos = 0;
    let mut depth = 0;
    let mut builder = GreenNodeBuilder::new();
    let mut errors = Vec::new();
    for event in parser.events {
        match event {
            Event::Begin { kind } => {
                if depth > 0 {
                    while token_pos < all_tokens.len() {
                        let kind = all_tokens[token_pos];
                        if !kind.is_trivia() {
                            break;
                        }
                        builder.token(kind.to_rowan(), &s[all_tokens_text_range[token_pos]]);
                        token_pos += 1;
                    }
                }
                depth += 1;
                builder.start_node(kind.to_rowan());
            }
            Event::Token { kind, n_input } => {
                while token_pos < all_tokens.len() {
                    let kind = all_tokens[token_pos];
                    if !kind.is_trivia() {
                        break;
                    }
                    builder.token(kind.to_rowan(), &s[all_tokens_text_range[token_pos]]);
                    token_pos += 1;
                }
                if n_input == 1 {
                    let text = &s[all_tokens_text_range[token_pos]];
                    builder.token(kind.to_rowan(), text);
                } else {
                    let mut text = String::new();
                    for i in 0..n_input {
                        text.push_str(&s[all_tokens_text_range[token_pos + i]]);
                    }
                    builder.token(kind.to_rowan(), &text);
                }
                token_pos += n_input;
            }
            Event::Newline => {
                let kind = all_tokens[token_pos];
                let text = &s[all_tokens_text_range[token_pos]];
                assert_eq!(kind, Syntax::Newline);
                builder.token(kind.to_rowan(), text);
                token_pos += 1;
            }
            Event::End => {
                if depth == 1 {
                    while token_pos < all_tokens.len() {
                        let kind = all_tokens[token_pos];
                        let text = &s[all_tokens_text_range[token_pos]];
                        assert!(kind.is_trivia(), "{kind:?}, {text:?}");
                        builder.token(kind.to_rowan(), text);
                        token_pos += 1;
                    }
                }
                depth -= 1;
                builder.finish_node();
            }
            Event::Error { s } => {
                errors.push(s.into_string());
            },
        }
    }

    (builder.finish(), errors)
}

impl Syntax {
    fn to_rowan(self) -> rowan::SyntaxKind {
        <Language as rowan::Language>::kind_to_raw(self)
    }
}

pub(crate) struct MarkOpen(usize);

pub(crate) struct MarkClosed(usize);

impl Parser {
    pub(crate) fn nth(&self, n: usize) -> Syntax {
        assert!(self.fuel.get() > 0);
        self.fuel.set(self.fuel.get().saturating_sub(1));
        self.tokens
            .get(self.pos + n)
            .copied()
            .unwrap_or(Syntax::Eof)
    }

    pub(crate) fn at(&self, kind: Syntax) -> bool {
        self.nth_at(0, kind)
    }

    pub(crate) fn at_any(&self, kind: &[Syntax]) -> bool {
        kind.iter().copied().any(|kind| self.nth_at(0, kind))
    }

    pub(crate) fn nth_keyword(&self, n: usize) -> Syntax {
        self.tokens_keyword
            .get(self.pos + n)
            .copied()
            .unwrap_or(Syntax::Eof)
    }

    pub(crate) fn nth_at_keyword(&self, n: usize, kind: Syntax) -> bool {
        self.nth_keyword(n) == kind
    }

    pub(crate) fn at_keyword(&self, kind: Syntax) -> bool {
        self.nth_at_keyword(0, kind)
    }

    pub(crate) fn nth_joined(&self, n: usize) -> bool {
        !self
            .tokens_after_trivia
            .get(self.pos + n)
            .copied()
            .unwrap_or_default()
    }

    pub(crate) fn nth_at_newline(&self, n: usize) -> bool {
        self.tokens_after_newline
            .get(self.pos + n)
            .copied()
            .unwrap_or_default()
    }

    pub(crate) fn at_newline(&self) -> bool {
        self.nth_at_newline(0)
    }

    pub(crate) fn current(&self) -> Syntax {
        self.nth(0)
    }

    pub(crate) fn current_operator(&self) -> Syntax {
        self.nth_operator(0)
    }

    pub(crate) fn nth_operator(&self, n: usize) -> Syntax {
        match self.nth_keyword(n) {
            t!("identifier") if self.nth_at(n, t!("and")) => t!("and"),
            t!("identifier") if self.nth_at(n, t!("or")) => t!("or"),
            t!("!") if self.nth_at(n, t!("!=")) => t!("!="),
            t!("%") if self.nth_at(n, t!("%=")) => t!("%="),
            t!("&") if self.nth_at(n, t!("&=")) => t!("&="),
            t!("*") if self.nth_at(n, t!("*=")) => t!("*="),
            t!("+") if self.nth_at(n, t!("+=")) => t!("+="),
            t!("-") if self.nth_at(n, t!("-=")) => t!("-="),
            t!("/") if self.nth_at(n, t!("/=")) => t!("/="),
            t!("<") if self.nth_at(n, t!("<<")) => t!("<<"),
            t!("<") if self.nth_at(n, t!("<<=")) => t!("<<="),
            t!("<") if self.nth_at(n, t!("<=")) => t!("<="),
            t!("=") if self.nth_at(n, t!("==")) => t!("=="),
            t!(">") if self.nth_at(n, t!(">=")) => t!(">="),
            t!(">") if self.nth_at(n, t!(">>")) => t!(">>"),
            t!(">") if self.nth_at(n, t!(">>=")) => t!(">>="),
            t!("^") if self.nth_at(n, t!("^=")) => t!("^="),
            t!("|") if self.nth_at(n, t!("|=")) => t!("|="),
            other => other,
        }
    }

    pub(crate) fn begin(&mut self) -> MarkOpen {
        self.events.push(Event::Begin { kind: Syntax::Eof });
        MarkOpen(self.events.len() - 1)
    }

    pub(crate) fn begin_at(&mut self, MarkClosed(i): MarkClosed) -> MarkOpen {
        self.events.insert(i, Event::Begin { kind: Syntax::Eof });
        MarkOpen(i)
    }

    pub(crate) fn bump(&mut self, kind: Syntax) {
        assert!(self.at(kind) || self.at_keyword(kind));
        assert_ne!(kind, Syntax::Newline);
        self.fuel.set(u8::MAX);
        let n_input = if kind.decompose_3().is_some() {
            3
        } else if kind.decompose_2().is_some() {
            2
        } else {
            1
        };
        self.events.push(Event::Token { kind, n_input });
        self.pos += n_input;
    }

    pub(crate) fn bump_any(&mut self) {
        self.bump(self.current());
    }

    pub(crate) fn bump_newline(&mut self) {
        self.events.push(Event::Newline);
    }

    pub(crate) fn end(&mut self, MarkOpen(i): MarkOpen, kind: Syntax) -> MarkClosed {
        self.events[i] = Event::Begin { kind };
        self.events.push(Event::End);
        MarkClosed(i)
    }

    pub(crate) fn eat(&mut self, kind: Syntax) -> bool {
        if self.at(kind) {
            self.bump(kind);
            true
        } else {
            false
        }
    }

    pub(crate) fn eat_keyword(&mut self, kind: Syntax) -> bool {
        if self.at_keyword(kind) {
            self.bump(kind);
            true
        } else {
            false
        }
    }

    pub(crate) fn nth_at(&self, n: usize, kind: Syntax) -> bool {
        if let Some([t0, t1, t2]) = kind.decompose_3() {
            self.nth(n) == t0
                && self.nth(n + 1) == t1
                && self.nth_joined(n + 1)
                && self.nth(n + 2) == t2
                && self.nth_joined(n + 2)
        } else if let Some([t0, t1]) = kind.decompose_2() {
            self.nth(n) == t0 && self.nth(n + 1) == t1 && self.nth_joined(n + 1)
        } else {
            self.nth(n) == kind
        }
    }

    pub(crate) fn error(&mut self, s: &str) {
        self.events.push(Event::Error { s: String::from(s).into_boxed_str() })
    }

    pub(crate) fn expect(&mut self, kind: Syntax) {
        if !self.at(kind) {
            self.error(&format!("expected {kind:?}, at {:?}", self.current()));
            return;
        }
        self.bump(kind);
    }

    pub(crate) fn expect_keyword(&mut self, kind: Syntax) {
        if !self.at_keyword(kind) {
            self.error(&format!("expected {kind:?}, at {:?}", self.current()));
            return;
        }
        self.bump(kind);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SyntaxNode;
    use expect_test::{expect, Expect};

    #[test]
    fn test_parse() {
        fn check(src: &str, expected: Expect) {
            let (green, errors) = parse_file(src);
            assert!(errors.is_empty());
            expected.assert_debug_eq(&SyntaxNode::new_root(green));
        }
        check(
            "fn main() ptr u32 { return null }",
            expect![[r#"
                File@0..33
                  FnItem@0..33
                    FnKeyword@0..2 "fn"
                    Space@2..3 " "
                    Identifier@3..7 "main"
                    LeftParenthesis@7..8 "("
                    RightParenthesis@8..9 ")"
                    Space@9..10 " "
                    PointerType@10..17
                      PtrKeyword@10..13 "ptr"
                      Space@13..14 " "
                      NameType@14..17
                        Identifier@14..17 "u32"
                    Space@17..18 " "
                    BlockExpr@18..33
                      LeftCurlyBracket@18..19 "{"
                      Space@19..20 " "
                      ExprStmt@20..31
                        ReturnExpr@20..31
                          ReturnKeyword@20..26 "return"
                          Space@26..27 " "
                          NameExpr@27..31
                            Identifier@27..31 "null"
                      Space@31..32 " "
                      RightCurlyBracket@32..33 "}"

            "#]],
        );

        check(
            "fn fib(n u32) u32 {
                if n <= 1 {
                    return 1
                }
                return fib(n - 1) + fib(n - 2)
            }",
            expect![[r#"
                File@0..155
                  FnItem@0..155
                    FnKeyword@0..2 "fn"
                    Space@2..3 " "
                    Identifier@3..6 "fib"
                    LeftParenthesis@6..7 "("
                    Parameter@7..12
                      Identifier@7..8 "n"
                      Space@8..9 " "
                      NameType@9..12
                        Identifier@9..12 "u32"
                    RightParenthesis@12..13 ")"
                    Space@13..14 " "
                    NameType@14..17
                      Identifier@14..17 "u32"
                    Space@17..18 " "
                    BlockExpr@18..155
                      LeftCurlyBracket@18..19 "{"
                      Newline@19..20 "\n"
                      Space@20..36 "                "
                      ExprStmt@36..95
                        IfExpr@36..94
                          IfKeyword@36..38 "if"
                          Space@38..39 " "
                          BinaryExpr@39..45
                            NameExpr@39..40
                              Identifier@39..40 "n"
                            Space@40..41 " "
                            LessThanSignEqualsSign@41..43 "<="
                            Space@43..44 " "
                            LiteralExpr@44..45
                              Number@44..45 "1"
                          Space@45..46 " "
                          BlockExpr@46..94
                            LeftCurlyBracket@46..47 "{"
                            Newline@47..48 "\n"
                            Space@48..68 "                    "
                            ExprStmt@68..76
                              ReturnExpr@68..76
                                ReturnKeyword@68..74 "return"
                                Space@74..75 " "
                                LiteralExpr@75..76
                                  Number@75..76 "1"
                            Newline@76..77 "\n"
                            Space@77..93 "                "
                            RightCurlyBracket@93..94 "}"
                        Newline@94..95 "\n"
                      Space@95..111 "                "
                      ExprStmt@111..141
                        ReturnExpr@111..141
                          ReturnKeyword@111..117 "return"
                          Space@117..118 " "
                          BinaryExpr@118..141
                            CallExpr@118..128
                              NameExpr@118..121
                                Identifier@118..121 "fib"
                              LeftParenthesis@121..122 "("
                              Argument@122..127
                                BinaryExpr@122..127
                                  NameExpr@122..123
                                    Identifier@122..123 "n"
                                  Space@123..124 " "
                                  HyphenMinus@124..125 "-"
                                  Space@125..126 " "
                                  LiteralExpr@126..127
                                    Number@126..127 "1"
                              RightParenthesis@127..128 ")"
                            Space@128..129 " "
                            PlusSign@129..130 "+"
                            Space@130..131 " "
                            CallExpr@131..141
                              NameExpr@131..134
                                Identifier@131..134 "fib"
                              LeftParenthesis@134..135 "("
                              Argument@135..140
                                BinaryExpr@135..140
                                  NameExpr@135..136
                                    Identifier@135..136 "n"
                                  Space@136..137 " "
                                  HyphenMinus@137..138 "-"
                                  Space@138..139 " "
                                  LiteralExpr@139..140
                                    Number@139..140 "2"
                              RightParenthesis@140..141 ")"
                      Newline@141..142 "\n"
                      Space@142..154 "            "
                      RightCurlyBracket@154..155 "}"

            "#]],
        );
    }
}
