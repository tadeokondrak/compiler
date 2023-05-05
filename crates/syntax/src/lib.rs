pub mod ast;

use std::mem;

use lexer::lex;
use rowan::{GreenNode, GreenNodeBuilder};

#[allow(non_camel_case_types)]
#[repr(u16)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxKind {
    #[doc(hidden)]
    EOF,
    #[doc(hidden)]
    TOMBSTONE,

    // Tokens

    // Tokens straight from the lexer
    UNKNOWN,
    SPACE,
    COMMENT,
    IDENT,
    RAW_IDENT,
    INTEGER,
    CHARACTER,
    STRING,
    PLUS,
    MINUS,
    STAR,
    SLASH,
    PERCENT,
    LESS,
    GREATER,
    EQUAL,
    AMPERSAND,
    PIPE,
    CARET,
    TILDE,
    PERIOD,
    COMMA,
    COLON,
    SEMI,
    APOSTROPHE,
    AT,
    POUND,
    QUESTION,
    BANG,
    DOLLAR,
    BACKSLASH,
    LEFT_PAREN,
    RIGHT_PAREN,
    LEFT_BRACKET,
    RIGHT_BRACKET,
    LEFT_BRACE,
    RIGHT_BRACE,

    // Combined tokens
    LESS2,
    GREATER2,
    LESS_EQUAL,
    GREATER_EQUAL,

    // Keywords
    IF_KW,
    ELSE_KW,
    FOR_KW,
    WHILE_KW,
    FN_KW,
    RETURN_KW,
    CONST_KW,
    STATIC_KW,
    ENUM_KW,
    STRUCT_KW,
    EXTERN_KW,
    UNION_KW,
    LET_KW,

    // Nodes
    ERROR,
    ROOT,
    NAME,
    PARAM,
    PARAM_LIST,
    GENERIC_PARAM,
    GENERIC_PARAM_LIST,
    CONTAINER_FIELD,
    CONTAINER_FIELD_LIST,

    // Items
    FN_ITEM,
    CONST_ITEM,
    STATIC_ITEM,
    CONTAINER_ITEM,

    LITERAL_EXPR,
    IDENT_EXPR,
    BLOCK_EXPR,
    UNARY_EXPR,
    BINARY_EXPR,
    RETURN_EXPR,

    LET_STMT,

    IDENT_TYPE,
    SLICE_TYPE,

    #[doc(hidden)]
    __LAST,
}

use SyntaxKind::*;

pub type SyntaxNode = rowan::SyntaxNode<Language>;
pub type SyntaxToken = rowan::SyntaxToken<Language>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Language;

impl rowan::Language for Language {
    type Kind = SyntaxKind;

    fn kind_from_raw(rowan::SyntaxKind(raw): rowan::SyntaxKind) -> SyntaxKind {
        assert!(raw < SyntaxKind::__LAST as u16);
        unsafe { mem::transmute(raw) }
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Unop {
    Not,
    Neg,
}

#[derive(Copy, Clone, Debug)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    And,
    Or,
    Xor,
}

pub fn parse_root(s: &str) -> (GreenNode, Vec<String>) {
    let mut parser = Parser::new(s);
    parser.parse_root();
    (parser.builder.finish(), parser.errors)
}

struct Parser<'a> {
    input: &'a str,
    kinds: Vec<SyntaxKind>,
    lengths: Vec<usize>,
    pos: usize,
    text_pos: usize,
    builder: GreenNodeBuilder<'static>,
    errors: Vec<String>,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Parser<'a> {
        let mut kinds = Vec::new();
        let mut lengths = Vec::new();
        for token in lex(input) {
            use lexer::TokenKind::*;
            let syntax_kind = match token.kind {
                Unknown => UNKNOWN,
                Space => SPACE,
                Comment => COMMENT,
                Ident => IDENT,
                RawIdent => RAW_IDENT,
                Integer => INTEGER,
                Character => CHARACTER,
                String => STRING,
                Plus => PLUS,
                Minus => MINUS,
                Star => STAR,
                Slash => SLASH,
                Percent => PERCENT,
                Less => LESS,
                Greater => GREATER,
                Equal => EQUAL,
                Ampersand => AMPERSAND,
                Pipe => PIPE,
                Caret => CARET,
                Tilde => TILDE,
                Period => PERIOD,
                Comma => COMMA,
                Colon => COLON,
                Semi => SEMI,
                Apostrophe => APOSTROPHE,
                At => AT,
                Pound => POUND,
                Question => QUESTION,
                Bang => BANG,
                Dollar => DOLLAR,
                Backslash => BACKSLASH,
                LeftParen => LEFT_PAREN,
                RightParen => RIGHT_PAREN,
                LeftBracket => LEFT_BRACKET,
                RightBracket => RIGHT_BRACKET,
                LeftBrace => LEFT_BRACE,
                RightBrace => RIGHT_BRACE,
            };
            kinds.push(syntax_kind);
            lengths.push(token.len);
        }
        let parser = Parser {
            input,
            kinds,
            lengths,
            pos: 0,
            text_pos: 0,
            builder: GreenNodeBuilder::new(),
            errors: Vec::new(),
        };
        parser
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        let raw_kind = <Language as rowan::Language>::kind_to_raw(kind);
        self.builder.start_node(raw_kind);
    }

    fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    fn current_token_or_keyword(&self) -> SyntaxKind {
        let kind = self.current_token();
        match kind {
            IDENT => match self.current_token_text() {
                "if" => T![if],
                "else" => T![else],
                "for" => T![for],
                "while" => T![while],
                "fn" => T![fn],
                "return" => T![return],
                "const" => T![const],
                "static" => T![static],
                "enum" => T![enum],
                "struct" => T![struct],
                "extern" => T![extern],
                "union" => T![union],
                "let" => T![let],
                _ => IDENT,
            },
            _ => kind,
        }
    }

    fn current_token(&self) -> SyntaxKind {
        self.kinds.get(self.pos).copied().unwrap_or(EOF)
    }

    fn current_token_text(&self) -> &str {
        let len = self.lengths[self.pos];
        &self.input[self.text_pos..self.text_pos + len]
    }

    fn error(&mut self, message: &str) {
        self.errors.push(message.to_owned());
    }

    fn eat(&mut self, kind: SyntaxKind) -> bool {
        if self.is_at(kind) {
            self.bump_impl(kind);
            true
        } else {
            false
        }
    }

    fn bump(&mut self, kind: SyntaxKind) {
        assert!(self.is_at(kind));
        self.bump_impl(kind);
    }

    fn bump_any(&mut self) {
        self.bump_impl(self.current_token());
    }

    fn bump_impl(&mut self, kind: SyntaxKind) {
        if self.pos >= self.kinds.len() {
            return;
        }
        let raw_kind = <Language as rowan::Language>::kind_to_raw(kind);
        let text = {
            let len = self.lengths[self.pos];
            &self.input[self.text_pos..self.text_pos + len]
        };
        self.builder.token(raw_kind, text);
        self.pos += 1;
        self.text_pos += self.lengths[self.pos - 1];
    }

    fn eat_trivia(&mut self) {
        while self.is_at(SPACE) || self.is_at(COMMENT) {
            self.bump_any();
        }
    }

    fn is_at(&self, kind: SyntaxKind) -> bool {
        self.current_token() == kind || self.current_token_or_keyword() == kind
    }

    fn parse_root(&mut self) {
        self.start_node(ROOT);
        self.eat_trivia();
        while !self.is_at(EOF) {
            self.parse_item();
        }
        self.finish_node();
    }

    fn parse_item(&mut self) {
        self.eat_trivia();
        if self.is_at(T![fn]) {
            self.parse_fn();
        } else if self.is_at(T![const]) {
            self.parse_const();
        } else if self.is_at(T![static]) {
            self.parse_static();
        } else if self.is_at(T![enum]) || self.is_at(T![struct]) || self.is_at(T![union]) {
            self.parse_container();
        } else if !self.is_at(EOF) {
            self.error("expected item");
            self.start_node(ERROR);
            self.bump_any();
            self.finish_node();
        }
    }

    fn parse_fn(&mut self) {
        self.start_node(FN_ITEM);
        self.bump(T![fn]);
        self.finish_node();
    }

    fn parse_const(&mut self) {
        self.start_node(CONST_ITEM);
        self.bump(T![const]);
        self.eat(IDENT);
        if self.eat(T![:]) {
            self.parse_type();
        }
        self.eat(T![=]);
        self.parse_expr();
        self.finish_node();
    }

    fn parse_static(&mut self) {
        self.start_node(STATIC_ITEM);
        self.bump(T![static]);
        self.eat(IDENT);
        if self.eat(T![:]) {
            self.eat_trivia();
            self.parse_type();
        }
        self.eat(T![=]);
        self.parse_expr();
        self.eat(SEMI);
        self.finish_node();
    }

    fn parse_container(&mut self) {
        self.start_node(CONTAINER_ITEM);
        assert!(self.eat(T![enum]) || self.eat(T![struct]) || self.eat(T![union]));
        self.eat_trivia();
        self.eat(IDENT);
        self.eat_trivia();
        self.start_node(CONTAINER_FIELD_LIST);
        if self.eat(T!['{']) {
            self.eat_trivia();
            while !self.eat(T!['}']) && !self.is_at(EOF) {
                self.eat_trivia();
                self.parse_container_field();
            }
        }
        self.finish_node();
        self.finish_node();
    }

    fn parse_container_field(&mut self) {
        self.start_node(CONTAINER_FIELD);
        self.eat_trivia();
        self.eat(IDENT);
        self.eat_trivia();
        self.eat(T![:]);
        self.eat_trivia();
        self.parse_type();
        self.eat_trivia();
        self.eat(SEMI);
        self.finish_node();
    }

    fn parse_type(&mut self) {
        if self.is_at(IDENT) {
            self.start_node(IDENT_TYPE);
            self.bump(IDENT);
            self.finish_node();
        } else if self.is_at(T!['[']) {
            self.start_node(SLICE_TYPE);
            self.bump(T!['[']);
            self.parse_type();
            self.eat(T![']']);
            self.finish_node();
        }
    }

    fn parse_stmt(&mut self) {}

    fn parse_expr(&mut self) {
        match self.current_token_or_keyword() {
            INTEGER | CHARACTER | STRING => {
                self.start_node(LITERAL_EXPR);
                self.bump_any();
                self.finish_node();
            }
            T![return] => {
                self.start_node(RETURN_EXPR);
                self.bump_any();
                self.parse_expr();
                self.finish_node();
            }
            IDENT => {
                self.start_node(IDENT_EXPR);
                self.bump_any();
                self.finish_node();
            }
            _ => {}
        }
    }
}

#[rustfmt::skip]
#[macro_export]
macro_rules! T {
    (+) => { SyntaxKind::PLUS };
    (-) => { SyntaxKind::MINUS };
    (*) => { SyntaxKind::STAR };
    (/) => { SyntaxKind::SLASH };
    (%) => { SyntaxKind::PERCENT };
    (-) => { SyntaxKind::LESS };
    (+) => { SyntaxKind::GREATER };
    (=) => { SyntaxKind::EQUAL };
    (+) => { SyntaxKind::AND };
    (|) => { SyntaxKind::BAR };
    (^) => { SyntaxKind::CARET };
    (~) => { SyntaxKind::TILDE };
    (.) => { SyntaxKind::PERIOD };
    (,) => { SyntaxKind::COMMA };
    (:) => { SyntaxKind::COLON };
    (;) => { SyntaxKind::SEMI };
    (@) => { SyntaxKind::AT };
    (#) => { SyntaxKind::POUND };
    (?) => { SyntaxKind::QUESTION };
    (!) => { SyntaxKind::BANG };
    ($) => { SyntaxKind::DOLLAR };
    (if) => { SyntaxKind::IF_KW };
    (else) => { SyntaxKind::ELSE_KW };
    (for) => { SyntaxKind::FOR_KW };
    (while) => { SyntaxKind::WHILE_KW };
    (fn) => { SyntaxKind::FN_KW };
    (return) => { SyntaxKind::RETURN_KW };
    (const) => { SyntaxKind::CONST_KW };
    (static) => { SyntaxKind::STATIC_KW };
    (enum) => { SyntaxKind::ENUM_KW };
    (struct) => { SyntaxKind::STRUCT_KW };
    (extern) => { SyntaxKind::EXTERN_KW };
    (union) => { SyntaxKind::UNION_KW };
    (let) => { SyntaxKind::LET_KW };
    ('\\') => { SyntaxKind::BACKSLASH };
    ('\'') => { SyntaxKind::APOSTROPHE };
    ('(') => { SyntaxKind::LEFT_PAREN };
    (')') => { SyntaxKind::RIGHT_PAREN };
    ('[') => { SyntaxKind::LEFT_BRACKET };
    (']') => { SyntaxKind::RIGHT_BRACKET };
    ('{') => { SyntaxKind::LEFT_BRACE };
    ('}') => { SyntaxKind::RIGHT_BRACE };
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};

    #[test]
    fn parse() {
        #[track_caller]
        fn check(s: &str, out: Expect) {
            let (green, errors) = parse_root(s);
            let root = SyntaxNode::new_root(green);
            out.assert_debug_eq(&root);
            assert!(errors.is_empty(), "{errors:?}");
        }

        check(
            "\
struct X {
    field: Uint8;
}

enum Y {
    variant;
}

union Z {
    variant: Y;
}
",
            expect![[r#"
                ROOT@0..85
                  CONTAINER_ITEM@0..30
                    STRUCT_KW@0..6 "struct"
                    SPACE@6..7 " "
                    IDENT@7..8 "X"
                    SPACE@8..9 " "
                    CONTAINER_FIELD_LIST@9..30
                      LEFT_BRACE@9..10 "{"
                      SPACE@10..15 "\n    "
                      CONTAINER_FIELD@15..28
                        IDENT@15..20 "field"
                        COLON@20..21 ":"
                        SPACE@21..22 " "
                        IDENT_TYPE@22..27
                          IDENT@22..27 "Uint8"
                        SEMI@27..28 ";"
                      SPACE@28..29 "\n"
                      CONTAINER_FIELD@29..29
                      RIGHT_BRACE@29..30 "}"
                  SPACE@30..32 "\n\n"
                  CONTAINER_ITEM@32..55
                    ENUM_KW@32..36 "enum"
                    SPACE@36..37 " "
                    IDENT@37..38 "Y"
                    SPACE@38..39 " "
                    CONTAINER_FIELD_LIST@39..55
                      LEFT_BRACE@39..40 "{"
                      SPACE@40..45 "\n    "
                      CONTAINER_FIELD@45..53
                        IDENT@45..52 "variant"
                        SEMI@52..53 ";"
                      SPACE@53..54 "\n"
                      CONTAINER_FIELD@54..54
                      RIGHT_BRACE@54..55 "}"
                  SPACE@55..57 "\n\n"
                  CONTAINER_ITEM@57..84
                    UNION_KW@57..62 "union"
                    SPACE@62..63 " "
                    IDENT@63..64 "Z"
                    SPACE@64..65 " "
                    CONTAINER_FIELD_LIST@65..84
                      LEFT_BRACE@65..66 "{"
                      SPACE@66..71 "\n    "
                      CONTAINER_FIELD@71..82
                        IDENT@71..78 "variant"
                        COLON@78..79 ":"
                        SPACE@79..80 " "
                        IDENT_TYPE@80..81
                          IDENT@80..81 "Y"
                        SEMI@81..82 ";"
                      SPACE@82..83 "\n"
                      CONTAINER_FIELD@83..83
                      RIGHT_BRACE@83..84 "}"
                  SPACE@84..85 "\n"

            "#]],
        );
    }
}
