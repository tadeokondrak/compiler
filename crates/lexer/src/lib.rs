//! The language's lexer.
//!
//! The API here is inspired by rustc's lexer.

use std::borrow::Cow;
use unicode_ident::{is_xid_continue, is_xid_start};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub len: usize,
}

impl Token {
    fn empty() -> Token {
        Token {
            kind: TokenKind::Unknown,
            len: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
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
}

fn parse_delim(s: &str, delim: char) -> Option<Cow<'_, str>> {
    let inner = s.strip_prefix(delim)?.strip_suffix(delim)?;
    if !inner.contains(delim) {
        Some(Cow::Borrowed(s))
    } else {
        let mut buf = String::new();
        let mut it = inner.chars();
        while let Some(c) = it.next() {
            if c == delim {
                if let Some(delim) = it.next() {
                    buf.push(delim);
                } else {
                    return None;
                }
            } else {
                buf.push(c);
            }
        }
        Some(Cow::Owned(buf))
    }
}

pub fn parse_raw_ident(s: &str) -> Option<Cow<'_, str>> {
    parse_delim(s, '`')
}

pub fn parse_integer(s: &str) -> Option<u64> {
    s.parse::<u64>().ok()
}

pub fn parse_character(s: &str) -> Option<char> {
    let inner = s.strip_prefix('\'')?.strip_suffix('\'')?;
    let mut it = inner.chars();
    let c = it.next()?;
    match c {
        '\\' => match it.next()? {
            c @ ('\\' | '\'') => {
                if it.next().is_some() {
                    return None;
                }
                Some(c)
            }
            _ => None,
        },
        _ => {
            if it.next().is_some() {
                return None;
            }
            Some(c)
        }
    }
}

pub fn parse_string(s: &str) -> Option<Cow<'_, str>> {
    parse_delim(s, '"')
}

pub fn lex_one(s: &str) -> Token {
    if s.is_empty() {
        return Token::empty();
    }
    let mut it = s.chars();
    let Some(first_char) = it.next() else { return Token::empty(); };
    let simple_token = match first_char {
        '+' => Some(TokenKind::Plus),
        '-' => Some(TokenKind::Minus),
        '*' => Some(TokenKind::Star),
        '%' => Some(TokenKind::Percent),
        '<' => Some(TokenKind::Less),
        '>' => Some(TokenKind::Greater),
        '=' => Some(TokenKind::Equal),
        '&' => Some(TokenKind::Ampersand),
        '|' => Some(TokenKind::Pipe),
        '^' => Some(TokenKind::Caret),
        '~' => Some(TokenKind::Tilde),
        '.' => Some(TokenKind::Period),
        ',' => Some(TokenKind::Comma),
        ':' => Some(TokenKind::Colon),
        ';' => Some(TokenKind::Semi),
        '@' => Some(TokenKind::At),
        '#' => Some(TokenKind::Pound),
        '?' => Some(TokenKind::Question),
        '!' => Some(TokenKind::Bang),
        '$' => Some(TokenKind::Dollar),
        '\\' => Some(TokenKind::Backslash),
        '(' => Some(TokenKind::LeftParen),
        ')' => Some(TokenKind::RightParen),
        '[' => Some(TokenKind::LeftBracket),
        ']' => Some(TokenKind::RightBracket),
        '{' => Some(TokenKind::LeftBrace),
        '}' => Some(TokenKind::RightBrace),
        _ => None,
    };
    if let Some(kind) = simple_token {
        return Token { kind, len: 1 };
    }
    let mut len = 1;
    match first_char {
        '\t' | '\n' | '\r' | ' ' => loop {
            match it.next() {
                Some('\t' | '\n' | '\r' | ' ') => {
                    len += 1;
                }
                Some(_) | None => {
                    break Token {
                        kind: TokenKind::Space,
                        len,
                    };
                }
            }
        },
        '0'..='9' => loop {
            match it.next() {
                Some(c) if c.is_ascii_alphanumeric() || c == '_' => {
                    len += 1;
                }
                Some(_) | None => {
                    break Token {
                        kind: TokenKind::Integer,
                        len,
                    };
                }
            }
        },
        c if is_xid_start(c) || c == '_' => loop {
            match it.next() {
                Some(c) if is_xid_continue(c) => {
                    len += c.len_utf8();
                }
                Some(_) | None => {
                    break Token {
                        kind: TokenKind::Ident,
                        len,
                    };
                }
            }
        },
        '\'' => {
            if s.starts_with(r#"'\'"#) {
                Token {
                    kind: TokenKind::Character,
                    len: 3,
                }
            } else if s.starts_with(r#"'\\'"#) {
                Token {
                    kind: TokenKind::Character,
                    len: 4,
                }
            } else {
                match it.next() {
                    Some(c) if c != '\'' && it.next() == Some('\'') => Token {
                        kind: TokenKind::Character,
                        len: c.len_utf8() + 2,
                    },
                    _ => Token {
                        kind: TokenKind::Apostrophe,
                        len: 1,
                    },
                }
            }
        }
        delim @ ('`' | '"') => {
            let mut escaped = false;
            loop {
                match it.next() {
                    Some('\\') if !escaped => {
                        len += 1;
                        escaped = true;
                    }
                    Some(c) if c == delim && !escaped => {
                        len += 1;
                        break Token {
                            kind: match delim {
                                '`' => TokenKind::RawIdent,
                                '"' => TokenKind::String,
                                _ => unreachable!(),
                            },
                            len,
                        };
                    }
                    Some(c) => {
                        len += c.len_utf8();
                        escaped = false;
                    }
                    None => {
                        break Token {
                            kind: TokenKind::Unknown,
                            len,
                        };
                    }
                }
            }
        }
        '/' => match it.next() {
            Some('/') => {
                len += 1;
                loop {
                    match it.next() {
                        c @ (Some('\n') | None) => {
                            if c.is_some() {
                                len += 1;
                            }
                            break Token {
                                kind: TokenKind::Comment,
                                len,
                            };
                        }
                        Some(c) => {
                            len += c.len_utf8();
                        }
                    }
                }
            }
            _ => Token {
                kind: TokenKind::Slash,
                len,
            },
        },
        _ => Token {
            kind: TokenKind::Unknown,
            len,
        },
    }
}

pub fn lex(mut s: &str) -> impl Iterator<Item = Token> + '_ {
    std::iter::from_fn(move || {
        if s.is_empty() {
            return None;
        }
        let token = lex_one(s);
        s = &s[token.len..];
        Some(token)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer() {
        use TokenKind::*;

        #[track_caller]
        fn check(s: &str, tokens: &[TokenKind]) {
            let got_tokens = lex(s).map(|token| token.kind).collect::<Vec<_>>();
            assert_eq!(got_tokens, tokens);
        }

        check("\t ", &[Space]);
        check("\t\t", &[Space]);
        check("!", &[Bang]);
        check("\\", &[Backslash]);
        check("`test`", &[RawIdent]);
        check("`te\\`st`", &[RawIdent]);
        check("'a", &[Apostrophe, Ident]);
        check("'_", &[Apostrophe, Ident]);
        check("'test", &[Apostrophe, Ident]);
        check("'a'", &[Character]);
        check("'\\'", &[Character]);
        check("'''", &[Apostrophe, Apostrophe, Apostrophe]);
        check("10", &[Integer]);
        check("/", &[Slash]);
        check("//", &[Comment]);
        check("//\n", &[Comment]);
        check("//hello", &[Comment]);
        check("//hello\nworld", &[Comment, Ident]);
    }
}
