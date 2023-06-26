#![allow(dead_code)]

use rowan::{GreenNode, GreenToken, Language as _, NodeOrToken, TextRange};
use std::cell::Cell;
use text_size::TextSize;

type SyntaxNode = rowan::SyntaxNode<Language>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Language {}

impl rowan::Language for Language {
    type Kind = SyntaxKind;

    fn kind_from_raw(rowan::SyntaxKind(raw): rowan::SyntaxKind) -> SyntaxKind {
        assert!(raw <= (SyntaxKind::Invalid as u16));
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw) }
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

#[repr(u16)]
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxKind {
    // Token kinds
    Eof = 0,
    // Lexer token kinds
    Unknown,
    Space,
    Comment,
    Ident,
    RawIdent,
    Integer,
    Character,
    String,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Less,
    Greater,
    Equal,
    Ampersand,
    Pipe,
    Caret,
    Tilde,
    Period,
    Comma,
    Colon,
    Semi,
    Apostrophe,
    At,
    Pound,
    Question,
    Bang,
    Dollar,
    Backslash,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    // Composite token kinds
    // Contextual token kinds
    FnKeyword,
    IfKeyword,
    StructKeyword,

    // Node kinds
    Error,
    // Miscellaneous containers
    Name,
    File,
    Block,
    Param,
    Params,
    // Declarations
    FnDecl,
    StructDecl,
    // Statements
    IfStmt,

    // Not a node or token kind
    // Used for conversions and as a placeholder
    Invalid,
}

impl From<lexer::TokenKind> for SyntaxKind {
    fn from(x: lexer::TokenKind) -> Self {
        match x {
            lexer::TokenKind::Unknown => SyntaxKind::Unknown,
            lexer::TokenKind::Space => SyntaxKind::Space,
            lexer::TokenKind::Comment => SyntaxKind::Comment,
            lexer::TokenKind::Ident => SyntaxKind::Ident,
            lexer::TokenKind::RawIdent => SyntaxKind::RawIdent,
            lexer::TokenKind::Integer => SyntaxKind::Integer,
            lexer::TokenKind::Character => SyntaxKind::Character,
            lexer::TokenKind::String => SyntaxKind::String,
            lexer::TokenKind::Plus => SyntaxKind::Plus,
            lexer::TokenKind::Minus => SyntaxKind::Minus,
            lexer::TokenKind::Star => SyntaxKind::Star,
            lexer::TokenKind::Slash => SyntaxKind::Slash,
            lexer::TokenKind::Percent => SyntaxKind::Percent,
            lexer::TokenKind::Less => SyntaxKind::Less,
            lexer::TokenKind::Greater => SyntaxKind::Greater,
            lexer::TokenKind::Equal => SyntaxKind::Equal,
            lexer::TokenKind::Ampersand => SyntaxKind::Ampersand,
            lexer::TokenKind::Pipe => SyntaxKind::Pipe,
            lexer::TokenKind::Caret => SyntaxKind::Caret,
            lexer::TokenKind::Tilde => SyntaxKind::Tilde,
            lexer::TokenKind::Period => SyntaxKind::Period,
            lexer::TokenKind::Comma => SyntaxKind::Comma,
            lexer::TokenKind::Colon => SyntaxKind::Colon,
            lexer::TokenKind::Semi => SyntaxKind::Semi,
            lexer::TokenKind::Apostrophe => SyntaxKind::Apostrophe,
            lexer::TokenKind::At => SyntaxKind::At,
            lexer::TokenKind::Pound => SyntaxKind::Pound,
            lexer::TokenKind::Question => SyntaxKind::Question,
            lexer::TokenKind::Bang => SyntaxKind::Bang,
            lexer::TokenKind::Dollar => SyntaxKind::Dollar,
            lexer::TokenKind::Backslash => SyntaxKind::Backslash,
            lexer::TokenKind::LeftParen => SyntaxKind::LeftParen,
            lexer::TokenKind::RightParen => SyntaxKind::RightParen,
            lexer::TokenKind::LeftBracket => SyntaxKind::LeftBracket,
            lexer::TokenKind::RightBracket => SyntaxKind::RightBracket,
            lexer::TokenKind::LeftBrace => SyntaxKind::LeftBrace,
            lexer::TokenKind::RightBrace => SyntaxKind::RightBrace,
        }
    }
}

#[rustfmt::skip]
macro_rules! T {
    (+) => { SyntaxKind::Plus };
    (-) => { SyntaxKind::Minus };
    (*) => { SyntaxKind::Star };
    (/) => { SyntaxKind::Slash };
    (%) => { SyntaxKind::Percent };
    (<) => { SyntaxKind::Less };
    (>) => { SyntaxKind::Greater };
    (=) => { SyntaxKind::Equal };
    (&) => { SyntaxKind::Ampersand };
    (|) => { SyntaxKind::Pipe };
    (^) => { SyntaxKind::Caret };
    (~) => { SyntaxKind::Tilde };
    (.) => { SyntaxKind::Period };
    (,) => { SyntaxKind::Comma };
    (:) => { SyntaxKind::Colon };
    (;) => { SyntaxKind::Semi };
    ('\'') => { SyntaxKind::Apostrophe };
    (@) => { SyntaxKind::At };
    (#) => { SyntaxKind::Pound };
    (?) => { SyntaxKind::Question };
    (!) => { SyntaxKind::Bang };
    ($) => { SyntaxKind::Dollar };
    ('\\') => { SyntaxKind::Backslash };
    ('(') => { SyntaxKind::LeftParen };
    (')') => { SyntaxKind::RightParen };
    ('[') => { SyntaxKind::LeftBracket };
    (']') => { SyntaxKind::RightBracket };
    ('{') => { SyntaxKind::LeftBrace };
    ('}') => { SyntaxKind::RightBrace };
    (if) => { SyntaxKind::IfKeyword };
    (fn) => { SyntaxKind::FnKeyword };
    (struct) => { SyntaxKind::StructKeyword };
}

impl SyntaxKind {
    fn is_contextual_keyword(self) -> bool {
        matches!(self, T![fn] | T![if] | T![struct])
    }

    fn is_trivia(self) -> bool {
        matches!(self, SyntaxKind::Space | SyntaxKind::Comment)
    }
}

fn keyword(s: &str) -> Option<SyntaxKind> {
    match s {
        "fn" => Some(T![fn]),
        "if" => Some(T![if]),
        "struct" => Some(T![struct]),
        _ => None,
    }
}

pub fn parse(s: &str) -> (GreenNode, Vec<String>) {
    let mut kinds: Vec<SyntaxKind> = Vec::new();
    let mut non_trivia_kinds: Vec<SyntaxKind> = Vec::new();
    let mut non_trivia_contextual_kinds: Vec<SyntaxKind> = Vec::new();
    let mut non_trivia_joins: Vec<bool> = Vec::new();
    let mut lengths: Vec<TextSize> = Vec::new();
    let mut last_was_trivia = true;
    let mut pos = 0;
    for lexer::Token { kind, len } in lexer::lex(s) {
        let kind: SyntaxKind = kind.into();
        kinds.push(kind);
        lengths.push(len.try_into().expect("token too long"));
        let is_trivia = kind.is_trivia();
        if !is_trivia {
            non_trivia_kinds.push(kind);
            non_trivia_joins.push(!last_was_trivia);
            let contextual_kind = match kind {
                SyntaxKind::Ident => match keyword(&s[pos..pos + len]) {
                    Some(keyword) => keyword,
                    None => kind,
                },
                _ => kind,
            };
            non_trivia_contextual_kinds.push(contextual_kind);
        }
        last_was_trivia = is_trivia;
        pos += len;
    }

    let mut parser = Parser {
        pos: 0,
        kinds: non_trivia_kinds,
        contextual_kinds: non_trivia_contextual_kinds,
        joins: non_trivia_joins,
        events: Vec::new(),
        errors: Vec::new(),
        fuel: Cell::new(u8::MAX),
    };

    parse_file(&mut parser);

    let node = build_node(parser.events, kinds, lengths, s);

    (node, parser.errors)
}

fn build_node(
    events: Vec<Event>,
    kinds: Vec<SyntaxKind>,
    lengths: Vec<TextSize>,
    s: &str,
) -> GreenNode {
    let mut text_pos = TextSize::default();
    let mut token_pos = 0;
    let mut stack: Vec<Vec<NodeOrToken<GreenNode, GreenToken>>> = vec![Vec::new()];

    for event in events {
        match event {
            Event::Start => {
                stack.push(Vec::new());
                eat_trivia(&kinds, &mut token_pos, &lengths, &mut text_pos, s, &mut stack);
            }
            Event::Token { kind, consumed } => {
                let mut len = TextSize::default();
                for _ in 0..consumed {
                    len += lengths[token_pos];
                    token_pos += 1;
                }
                let range = TextRange::new(text_pos, text_pos + len);
                let text = &s[range];
                let token = GreenToken::new(Language::kind_to_raw(kind), text);
                eprintln!("token: {:?} {:?}", token, text);
                stack.last_mut().unwrap().push(NodeOrToken::Token(token));
                text_pos += len;
                eat_trivia(&kinds, &mut token_pos, &lengths, &mut text_pos, s, &mut stack);
            }
            Event::Finish { kind } => {
                let node = GreenNode::new(
                    rowan::SyntaxKind(kind as u16),
                    stack.pop().unwrap().into_iter(),
                );
                stack.last_mut().unwrap().push(NodeOrToken::Node(node));
            }
        }
    }

    assert_eq!(stack.len(), 1);
    assert_eq!(stack[0].len(), 1);
    assert!(stack[0][0].as_node().is_some());

    fn eat_trivia(
        kinds: &[SyntaxKind],
        token_pos: &mut usize,
        lengths: &[TextSize],
        text_pos: &mut TextSize,
        s: &str,
        stack: &mut [Vec<NodeOrToken<GreenNode, GreenToken>>],
    ) {
        while kinds.get(*token_pos).copied().unwrap_or(SyntaxKind::Eof).is_trivia() {
            let trivia_kind = kinds[*token_pos];
            let trivia_len = lengths[*token_pos];
            let trivia_range = TextRange::new(*text_pos, *text_pos + trivia_len);
            let trivia_text = &s[trivia_range];
            let token = GreenToken::new(Language::kind_to_raw(trivia_kind), trivia_text);
            stack.last_mut().unwrap().push(NodeOrToken::Token(token));
            *token_pos += 1;
            *text_pos += trivia_len;
        }
    }

    stack
        .into_iter()
        .next()
        .unwrap()
        .into_iter()
        .find_map(NodeOrToken::into_node)
        .unwrap()
}

#[test]
fn test() {
    let (node, errors) = parse(
        "
            fn main(a u32, b u32, c u32) u32 {
                if x {}
            }

            struct X {
            }
        ",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let expected = expect_test::expect![[r#"
        File@0..132
          Space@0..13 "\n            "
          FnDecl@13..99
            FnKeyword@13..15 "fn"
            Space@15..16 " "
            Name@16..20
              Ident@16..20 "main"
            Params@20..42
              LeftParen@20..21 "("
              Param@21..28
                Name@21..23
                  Ident@21..22 "a"
                  Space@22..23 " "
                Name@23..26
                  Ident@23..26 "u32"
                Comma@26..27 ","
                Space@27..28 " "
              Param@28..35
                Name@28..30
                  Ident@28..29 "b"
                  Space@29..30 " "
                Name@30..33
                  Ident@30..33 "u32"
                Comma@33..34 ","
                Space@34..35 " "
              Param@35..40
                Name@35..37
                  Ident@35..36 "c"
                  Space@36..37 " "
                Name@37..40
                  Ident@37..40 "u32"
              RightParen@40..41 ")"
              Space@41..42 " "
            Name@42..46
              Ident@42..45 "u32"
              Space@45..46 " "
            Block@46..99
              LeftBrace@46..47 "{"
              Space@47..64 "\n                "
              IfStmt@64..84
                IfKeyword@64..66 "if"
                Space@66..67 " "
                Name@67..69
                  Ident@67..68 "x"
                  Space@68..69 " "
                Block@69..84
                  LeftBrace@69..70 "{"
                  RightBrace@70..71 "}"
                  Space@71..84 "\n            "
              RightBrace@84..85 "}"
              Space@85..99 "\n\n            "
          StructDecl@99..132
            StructKeyword@99..105 "struct"
            Space@105..106 " "
            Name@106..108
              Ident@106..107 "X"
              Space@107..108 " "
            LeftBrace@108..109 "{"
            Space@109..122 "\n            "
            RightBrace@122..123 "}"
            Space@123..132 "\n        "

    "#]];
    expected.assert_debug_eq(&SyntaxNode::new_root(node));
}

struct Parser {
    pos: usize,
    kinds: Vec<SyntaxKind>,
    contextual_kinds: Vec<SyntaxKind>,
    joins: Vec<bool>,
    events: Vec<Event>,
    errors: Vec<String>,
    fuel: Cell<u8>,
}

impl Parser {
    fn nth(&self, n: usize) -> SyntaxKind {
        self.fuel.set(self.fuel.get().saturating_sub(1));
        if self.fuel.get() == 0 {
            panic!("out of fuel");
        }

        self.kinds
            .get(self.pos + n)
            .copied()
            .unwrap_or(SyntaxKind::Eof)
    }

    fn nth_contextual(&self, n: usize) -> SyntaxKind {
        self.fuel.set(self.fuel.get().saturating_sub(1));
        if self.fuel.get() == 0 {
            panic!("out of fuel");
        }

        self.contextual_kinds
            .get(self.pos + n)
            .copied()
            .unwrap_or(SyntaxKind::Eof)
    }

    fn at(&self, kind: SyntaxKind) -> bool {
        if kind.is_contextual_keyword() {
            self.nth_contextual(0) == kind
        } else {
            self.nth(0) == kind
        }
    }

    fn eat(&mut self, kind: SyntaxKind) -> bool {
        if self.at(kind) {
            self.bump(kind);
            true
        } else {
            false
        }
    }

    fn bump(&mut self, kind: SyntaxKind) {
        let consumed = 1;
        self.events.push(Event::Token { kind, consumed });
        self.pos += consumed;
    }

    fn bump_any(&mut self) {
        self.bump(self.nth(0));
    }

    fn expect(&mut self, kind: SyntaxKind) {
        if !self.eat(kind) {
            self.error(format!("expected {:?}, got {:?}", kind, self.nth(0)));
        }
    }

    fn expected(&mut self, text: &str) {
        self.error(format!(
            "expected {}, got {:?}",
            text,
            self.nth_contextual(0)
        ));
    }

    fn error(&mut self, text: String) {
        self.errors.push(text);
    }

    #[must_use]
    fn start(&mut self) -> Marker {
        self.events.push(Event::Start);
        Marker
    }

    fn finish(&mut self, marker: Marker, kind: SyntaxKind) {
        self.events.push(Event::Finish { kind });
        std::mem::forget(marker);
    }
}

struct Marker;

impl Drop for Marker {
    fn drop(&mut self) {
        panic!()
    }
}

#[derive(Debug)]
enum Event {
    Start,
    Token { kind: SyntaxKind, consumed: usize },
    Finish { kind: SyntaxKind },
}

fn parse_file(p: &mut Parser) {
    let m = p.start();
    while !p.at(SyntaxKind::Eof) {
        parse_decl(p);
    }
    p.finish(m, SyntaxKind::File);
}

fn parse_decl(p: &mut Parser) {
    if p.at(T![fn]) {
        parse_fn_decl(p);
    } else if p.at(T![struct]) {
        parse_struct_decl(p);
    } else {
        p.expected("declaration");
    }
}

fn parse_struct_decl(p: &mut Parser) {
    let m = p.start();
    p.bump(T![struct]);
    parse_name(p);
    p.expect(T!['{']);
    while !p.at(T!['}']) && !p.at(SyntaxKind::Eof) {
        parse_stmt(p);
    }
    p.expect(T!['}']);
    p.finish(m, SyntaxKind::StructDecl);
}

fn parse_fn_decl(p: &mut Parser) {
    let m = p.start();
    p.bump(T![fn]);
    parse_name(p);
    parse_params(p);
    parse_type_expr(p);
    parse_block(p);
    p.finish(m, SyntaxKind::FnDecl);
}

fn parse_block(p: &mut Parser) {
    let m = p.start();
    p.expect(T!['{']);
    while !p.at(T!['}']) && !p.at(SyntaxKind::Eof) {
        parse_stmt(p);
    }
    p.expect(T!['}']);
    p.finish(m, SyntaxKind::Block);
}

fn parse_stmt(p: &mut Parser) {
    let m = p.start();
    if p.at(T![if]) {
        parse_if_stmt(p, m);
    } else {
        p.bump_any();
        p.expected("statement");
        p.finish(m, SyntaxKind::Error);
    }
}

fn parse_if_stmt(p: &mut Parser, m: Marker) {
    p.bump(T![if]);
    parse_expr(p);
    parse_block(p);
    p.finish(m, SyntaxKind::IfStmt);
}

fn parse_expr(p: &mut Parser) {
    parse_name(p);
}

fn parse_type_expr(p: &mut Parser) {
    parse_name(p);
}

fn parse_params(p: &mut Parser) {
    let m = p.start();
    p.expect(T!['(']);
    while p.at(SyntaxKind::Ident) && !p.at(T![')']) && !p.at(SyntaxKind::Eof) {
        parse_param(p);
    }
    p.expect(T![')']);
    p.finish(m, SyntaxKind::Params);
}

fn parse_param(p: &mut Parser) {
    let m = p.start();
    parse_name(p);
    parse_type_expr(p);
    if !p.at(T![')']) {
        p.eat(T![,]);
    }
    p.finish(m, SyntaxKind::Param);
}

fn parse_name(p: &mut Parser) {
    let m = p.start();
    match p.nth(0) {
        SyntaxKind::Ident => {
            let contextual = p.nth_contextual(0);
            if contextual != SyntaxKind::Ident {
                p.expected("name");
            }
            p.bump(SyntaxKind::Ident);
            p.finish(m, SyntaxKind::Name);
        }
        SyntaxKind::RawIdent => {
            p.bump(SyntaxKind::RawIdent);
            p.finish(m, SyntaxKind::Name);
        }
        _ => {
            p.expected("name");
            p.finish(m, SyntaxKind::Error);
        }
    }
}