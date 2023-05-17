use lexer::{lex, Token as LexerToken, TokenKind as LexerTokenKind};
use std::fmt::{self};
use text_size::{TextRange, TextSize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    /// End of file.
    Eof,
    /// Unrecognized text.
    Unknown,

    /// A sequence of `{'\t', '\r', '\n', ' '}`
    Space,
    /// `// Line comment`
    Comment,

    /// `name`
    Ident,
    /// `` `name` ``
    RawIdent,

    /// `0`
    Integer,
    /// `'text'`
    Character,
    /// `"text"`
    String,

    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `%`
    Percent,

    /// `<`
    Less,
    /// `>`
    Greater,
    /// `=`
    Equal,

    /// `&`
    Ampersand,
    /// `|`
    Pipe,
    /// `^`
    Caret,
    /// `~`
    Tilde,

    /// `.`
    Period,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// `;`
    Semi,
    /// `'`
    Apostrophe,
    /// `@`
    At,
    /// `#`
    Pound,
    /// `?`
    Question,
    /// `!`
    Bang,
    /// `$`
    Dollar,
    /// `\`
    Backslash,

    /// `(`
    LeftParen,
    /// `)`
    RightParen,

    /// `[`
    LeftBracket,
    /// `]`
    RightBracket,

    /// `{`
    LeftBrace,
    /// `}`
    RightBrace,

    FnKeyword,
}

impl TokenKind {
    fn from_lexer_kind(kind: LexerTokenKind) -> TokenKind {
        match kind {
            LexerTokenKind::Unknown => TokenKind::Unknown,
            LexerTokenKind::Space => TokenKind::Space,
            LexerTokenKind::Comment => TokenKind::Comment,
            LexerTokenKind::Ident => TokenKind::Ident,
            LexerTokenKind::RawIdent => TokenKind::RawIdent,
            LexerTokenKind::Integer => TokenKind::Integer,
            LexerTokenKind::Character => TokenKind::Character,
            LexerTokenKind::String => TokenKind::String,
            LexerTokenKind::Plus => TokenKind::Plus,
            LexerTokenKind::Minus => TokenKind::Minus,
            LexerTokenKind::Star => TokenKind::Star,
            LexerTokenKind::Slash => TokenKind::Slash,
            LexerTokenKind::Percent => TokenKind::Percent,
            LexerTokenKind::Less => TokenKind::Less,
            LexerTokenKind::Greater => TokenKind::Greater,
            LexerTokenKind::Equal => TokenKind::Equal,
            LexerTokenKind::Ampersand => TokenKind::Ampersand,
            LexerTokenKind::Pipe => TokenKind::Pipe,
            LexerTokenKind::Caret => TokenKind::Caret,
            LexerTokenKind::Tilde => TokenKind::Tilde,
            LexerTokenKind::Period => TokenKind::Period,
            LexerTokenKind::Comma => TokenKind::Comma,
            LexerTokenKind::Colon => TokenKind::Colon,
            LexerTokenKind::Semi => TokenKind::Semi,
            LexerTokenKind::Apostrophe => TokenKind::Apostrophe,
            LexerTokenKind::At => TokenKind::At,
            LexerTokenKind::Pound => TokenKind::Pound,
            LexerTokenKind::Question => TokenKind::Question,
            LexerTokenKind::Bang => TokenKind::Bang,
            LexerTokenKind::Dollar => TokenKind::Dollar,
            LexerTokenKind::Backslash => TokenKind::Backslash,
            LexerTokenKind::LeftParen => TokenKind::LeftParen,
            LexerTokenKind::RightParen => TokenKind::RightParen,
            LexerTokenKind::LeftBracket => TokenKind::LeftBracket,
            LexerTokenKind::RightBracket => TokenKind::RightBracket,
            LexerTokenKind::LeftBrace => TokenKind::LeftBrace,
            LexerTokenKind::RightBrace => TokenKind::RightBrace,
        }
    }
}

pub struct Token {
    pub kind: TokenKind,
    pub leading_trivia: String,
    pub text: String,
    pub trailing_trivia: String,
}

impl Token {
    fn text_len(&self) -> usize {
        self.leading_trivia.len() + self.text.len() + self.trailing_trivia.len()
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}({:?}, {:?}, {:?})",
            self.kind, self.leading_trivia, self.text, self.trailing_trivia
        )
    }
}

#[derive(Debug)]
pub struct Root {
    pub items: Vec<Item>,
    pub eof: Token,
}

#[derive(Debug)]
pub enum Item {
    Fn(FnItem),
}

#[derive(Debug)]
pub enum Ty {
    Invalid(Token),
    Ident(Ident),
    Slice(SliceTy),
}

#[derive(Debug)]
pub enum Expr {
    Unary(UnaryExpr),
    Binary(BinaryExpr),
}

#[derive(Debug)]
pub enum Stmt {
    Let(LetStmt),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Ident {
    pub token: Token,
}

#[derive(Debug)]
pub struct SliceTy {
    pub left_bracket: Token,
    pub right_bracket: Token,
    pub ty: Box<Ty>,
}

#[derive(Debug)]
pub struct LetStmt {
    pub let_kw: Token,
}

#[derive(Debug)]
pub struct UnaryExpr {
    pub operand: Box<Expr>,
}

#[derive(Debug)]
pub struct BinaryExpr {
    pub lhs: Box<Expr>,
    pub op: Token,
    pub rhs: Box<Expr>,
}

#[derive(Debug)]
pub struct FnItem {
    pub fn_kw: Token,
    pub name: Token,
    pub params: FnParams,
    pub left_bracket: Token,
    pub right_bracket: Token,
}

#[derive(Debug)]
pub struct FnParams {
    pub left_paren: Token,
    pub params: Vec<FnParam>,
    pub right_paren: Token,
}

#[derive(Debug)]
pub struct FnParam {
    pub name: Token,
    pub colon: Token,
    pub ty: Ty,
}

fn lexer_token_is_trivia(kind: LexerTokenKind) -> bool {
    matches!(
        kind,
        LexerTokenKind::Unknown | LexerTokenKind::Space | LexerTokenKind::Comment,
    )
}

struct Parser<'a> {
    src: &'a str,
    cur_idx: usize,
    text_pos: TextSize,
    token_kinds: Vec<LexerTokenKind>,
    token_lengths: Vec<TextSize>,
    token_joins: Vec<bool>, // TODO: use a bit set
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Parser<'a> {
        let mut kinds = Vec::new();
        let mut lengths = Vec::new();
        let mut joins = Vec::new();
        let mut last_was_space = false;
        for LexerToken { kind, len } in lex(src) {
            // TextSize can only store sizes up to about 4 gigabytes.
            // We don't support tokens that long.
            let len = TextSize::try_from(len).expect("token too long");
            kinds.push(kind);
            lengths.push(len);
            joins.push(last_was_space);
            last_was_space = lexer_token_is_trivia(kind);
        }

        Parser {
            src,
            cur_idx: 0,
            text_pos: TextSize::from(0),
            token_kinds: kinds,
            token_lengths: lengths,
            token_joins: joins,
        }
    }

    fn is_at(&self, kind: TokenKind) -> bool {
        if self.cur_idx >= self.token_kinds.len() {
            return kind == TokenKind::Eof;
        }
        let token = self.token_kinds[self.cur_idx];
        match kind {
            TokenKind::Eof => false,
            TokenKind::Unknown => token == LexerTokenKind::Unknown,
            TokenKind::Space => token == LexerTokenKind::Space,
            TokenKind::Comment => token == LexerTokenKind::Comment,
            TokenKind::Ident => token == LexerTokenKind::Ident,
            TokenKind::RawIdent => token == LexerTokenKind::RawIdent,
            TokenKind::Integer => token == LexerTokenKind::Integer,
            TokenKind::Character => token == LexerTokenKind::Character,
            TokenKind::String => token == LexerTokenKind::String,
            TokenKind::Plus => token == LexerTokenKind::Plus,
            TokenKind::Minus => token == LexerTokenKind::Minus,
            TokenKind::Star => token == LexerTokenKind::Star,
            TokenKind::Slash => token == LexerTokenKind::Slash,
            TokenKind::Percent => token == LexerTokenKind::Percent,
            TokenKind::Less => token == LexerTokenKind::Less,
            TokenKind::Greater => token == LexerTokenKind::Greater,
            TokenKind::Equal => token == LexerTokenKind::Equal,
            TokenKind::Ampersand => token == LexerTokenKind::Ampersand,
            TokenKind::Pipe => token == LexerTokenKind::Pipe,
            TokenKind::Caret => token == LexerTokenKind::Caret,
            TokenKind::Tilde => token == LexerTokenKind::Tilde,
            TokenKind::Period => token == LexerTokenKind::Period,
            TokenKind::Comma => token == LexerTokenKind::Comma,
            TokenKind::Colon => token == LexerTokenKind::Colon,
            TokenKind::Semi => token == LexerTokenKind::Semi,
            TokenKind::Apostrophe => token == LexerTokenKind::Apostrophe,
            TokenKind::At => token == LexerTokenKind::At,
            TokenKind::Pound => token == LexerTokenKind::Pound,
            TokenKind::Question => token == LexerTokenKind::Question,
            TokenKind::Bang => token == LexerTokenKind::Bang,
            TokenKind::Dollar => token == LexerTokenKind::Dollar,
            TokenKind::Backslash => token == LexerTokenKind::Backslash,
            TokenKind::LeftParen => token == LexerTokenKind::LeftParen,
            TokenKind::RightParen => token == LexerTokenKind::RightParen,
            TokenKind::LeftBracket => token == LexerTokenKind::LeftBracket,
            TokenKind::RightBracket => token == LexerTokenKind::RightBracket,
            TokenKind::LeftBrace => token == LexerTokenKind::LeftBrace,
            TokenKind::RightBrace => token == LexerTokenKind::RightBrace,
            // TODO
            TokenKind::FnKeyword => token == LexerTokenKind::Ident,
        }
    }

    fn skip_trivia(&mut self) {
        while self.cur_idx < self.token_kinds.len()
            && lexer_token_is_trivia(self.token_kinds[self.cur_idx])
        {
            self.bump_any();
        }
    }

    fn bump(&mut self, trivia_start: TextSize, token_start: TextSize, kind: TokenKind) -> Token {
        assert!(self.is_at(kind));
        self.bump_any();
        let end = self.text_pos;
        self.make_token(kind, trivia_start, TextRange::new(token_start, end), end)
    }

    fn expect_with_leading(&mut self, kind: TokenKind) -> Token {
        let trivia_start = self.text_pos;
        self.skip_trivia();
        let token_start = self.text_pos;
        if self.is_at(kind) {
            self.bump(trivia_start, token_start, kind)
        } else {
            let end = self.text_pos;
            self.make_token(kind, trivia_start, TextRange::new(token_start, end), end)
        }
    }

    fn bump_any_as_unknown(&mut self, trivia_start: TextSize) -> Token {
        let token_start = self.text_pos;
        self.bump_any();
        let end = self.text_pos;
        self.make_token(
            TokenKind::from_lexer_kind(self.token_kinds[self.cur_idx]),
            trivia_start,
            TextRange::new(token_start, end),
            end,
        )
    }

    fn bump_any(&mut self) {
        if self.cur_idx >= self.token_kinds.len() {
            return;
        }
        self.text_pos += self.token_lengths[self.cur_idx];
        self.cur_idx += 1;
    }

    fn make_token(
        &self,
        kind: TokenKind,
        trivia_start: TextSize,
        token: TextRange,
        trivia_end: TextSize,
    ) -> Token {
        Token {
            kind,
            leading_trivia: self.src[TextRange::new(trivia_start, token.start())].to_owned(),
            text: self.src[token].to_owned(),
            trailing_trivia: self.src[TextRange::new(token.end(), trivia_end)].to_owned(),
        }
    }

    fn parse_root(&mut self) -> Root {
        let mut items = Vec::new();
        loop {
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(eof) => break Root { items, eof },
            }
        }
    }

    fn parse_item(&mut self) -> Result<Item, Token> {
        let start = self.text_pos;
        self.skip_trivia();
        while !self.is_at(TokenKind::Eof) {
            if self.is_at(TokenKind::FnKeyword) {
                return Ok(Item::Fn(self.parse_fn_item(start)));
            }
            self.bump_any();
            self.skip_trivia();
        }
        let end = self.text_pos;
        Err(self.make_token(TokenKind::Eof, start, TextRange::new(end, end), end))
    }

    fn parse_fn_item(&mut self, trivia_start: TextSize) -> FnItem {
        FnItem {
            fn_kw: self.bump(trivia_start, self.text_pos, TokenKind::FnKeyword),
            name: self.expect_with_leading(TokenKind::Ident),
            params: self.parse_fn_params(),
            left_bracket: self.expect_with_leading(TokenKind::LeftBrace),
            right_bracket: self.expect_with_leading(TokenKind::RightBrace),
        }
    }

    fn parse_fn_params(&mut self) -> FnParams {
        let left_paren = self.expect_with_leading(TokenKind::LeftParen);
        let mut params = Vec::new();
        loop {
            match self.parse_fn_param() {
                Ok(param) => params.push(param),
                Err(right_paren) => {
                    break FnParams {
                        left_paren,
                        params,
                        right_paren,
                    }
                }
            }
        }
        //let right_paren = self.expect_with_leading(TokenKind::RightParen);
    }

    fn parse_fn_param(&mut self) -> Result<FnParam, Token> {
        let trivia_start = self.text_pos;
        self.skip_trivia();
        if self.is_at(TokenKind::RightParen) {
            return Err(self.bump(trivia_start, self.text_pos, TokenKind::RightParen));
        }
        Ok(FnParam {
            name: self.expect_with_leading(TokenKind::Ident),
            colon: self.expect_with_leading(TokenKind::Colon),
            ty: self.parse_ty(),
        })
    }

    fn parse_ty(&mut self) -> Ty {
        let trivia_start = self.text_pos;
        self.skip_trivia();
        let token_start = self.text_pos;
        if self.is_at(TokenKind::LeftBracket) {
            Ty::Slice(SliceTy {
                left_bracket: self.bump(trivia_start, token_start, TokenKind::LeftBracket),
                right_bracket: self.expect_with_leading(TokenKind::RightBracket),
                ty: Box::new(self.parse_ty()),
            })
        } else if self.is_at(TokenKind::Ident) {
            Ty::Ident(Ident {
                token: self.bump(trivia_start, token_start, TokenKind::Ident),
            })
        } else {
            Ty::Invalid(self.bump_any_as_unknown(trivia_start))
        }
    }
}

pub fn parse(src: &str) -> Root {
    Parser::new(src).parse_root()
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};

    #[test]
    fn test_parse() {
        fn check(src: &str, expected: Expect) {
            let actual = parse(src);
            expected.assert_debug_eq(&actual);
        }

        check(
            "",
            expect![[r#"
                Root {
                    items: [],
                    eof: Eof("", "", ""),
                }
            "#]],
        );

        check(
            "????",
            expect![[r#"
                Root {
                    items: [],
                    eof: Eof("????", "", ""),
                }
            "#]],
        );

        check(
            "fn main() {}",
            expect![[r#"
                Root {
                    items: [
                        Fn(
                            FnItem {
                                fn_kw: FnKeyword("", "fn", ""),
                                name: Ident(" ", "main", ""),
                                params: FnParams {
                                    left_paren: LeftParen("", "(", ""),
                                    params: [],
                                    right_paren: RightParen("", ")", ""),
                                },
                                left_bracket: LeftBrace(" ", "{", ""),
                                right_bracket: RightBrace("", "}", ""),
                            },
                        ),
                    ],
                    eof: Eof("", "", ""),
                }
            "#]],
        );

        check(
            "fn main(args: ???) {}",
            expect![[r#"
            Root {
                items: [
                    Fn(
                        FnItem {
                            fn_kw: FnKeyword("", "fn", ""),
                            name: Ident(" ", "main", ""),
                            params: FnParams {
                                left_paren: LeftParen("", "(", ""),
                                params: [
                                    FnParam {
                                        name: Ident("", "args", ""),
                                        colon: Colon("", ":", ""),
                                        ty: Invalid(
                                            Question(" ", "?", ""),
                                        ),
                                    },
                                    FnParam {
                                        name: Ident("", "", ""),
                                        colon: Colon("", "", ""),
                                        ty: Invalid(
                                            Question("", "?", ""),
                                        ),
                                    },
                                    FnParam {
                                        name: Ident("", "", ""),
                                        colon: Colon("", "", ""),
                                        ty: Invalid(
                                            RightParen("", "?", ""),
                                        ),
                                    },
                                ],
                                right_paren: RightParen("", ")", ""),
                            },
                            left_bracket: LeftBrace(" ", "{", ""),
                            right_bracket: RightBrace("", "}", ""),
                        },
                    ),
                ],
                eof: Eof("", "", ""),
            }
        "#]],
        );

        check(
            "fn main(args: []T) {}",
            expect![[r#"
                Root {
                    items: [
                        Fn(
                            FnItem {
                                fn_kw: FnKeyword("", "fn", ""),
                                name: Ident(" ", "main", ""),
                                params: FnParams {
                                    left_paren: LeftParen("", "(", ""),
                                    params: [
                                        FnParam {
                                            name: Ident("", "args", ""),
                                            colon: Colon("", ":", ""),
                                            ty: Slice(
                                                SliceTy {
                                                    left_bracket: LeftBracket(" ", "[", ""),
                                                    right_bracket: RightBracket("", "]", ""),
                                                    ty: Ident(
                                                        Ident {
                                                            token: Ident("", "T", ""),
                                                        },
                                                    ),
                                                },
                                            ),
                                        },
                                    ],
                                    right_paren: RightParen("", ")", ""),
                                },
                                left_bracket: LeftBrace(" ", "{", ""),
                                right_bracket: RightBrace("", "}", ""),
                            },
                        ),
                    ],
                    eof: Eof("", "", ""),
                }
            "#]],
        );
    }
}
