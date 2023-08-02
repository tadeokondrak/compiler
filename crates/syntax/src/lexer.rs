use crate::Syntax;
use unicode_ident::{is_xid_continue, is_xid_start};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Lexeme {
    Error,
    Space,
    Newline,
    Comment,
    Identifier,
    Punctuation,
    NumberLiteral,
    StringLiteral,
    CharacterLiteral,
}

pub(crate) fn lex(s: &str) -> (Lexeme, usize) {
    let mut iter = s.chars();
    let Some(c) = iter.next() else {
        return (Lexeme::Error, 0);
    };
    match c {
        '0'..='9' => {
            let len = c.len_utf8() + iter.take_while(|&c| is_xid_continue(c)).count();
            (Lexeme::NumberLiteral, len)
        }
        '/' | '\\' if iter.next() == Some(c) => {
            let lexeme = match c {
                '/' => Lexeme::Comment,
                '\\' => Lexeme::StringLiteral,
                _ => unreachable!(),
            };
            let len = s.find(&['\r', '\n']).unwrap_or(s.len());
            (lexeme, len)
        }
        'A'..='Z' | 'a'..='z' | '_' | '\x7F'.. => {
            if is_xid_start(c) {
                let len = c.len_utf8()
                    + iter
                        .take_while(|&c| is_xid_continue(c))
                        .map(|c| c.len_utf8())
                        .sum::<usize>();
                (Lexeme::Identifier, len)
            } else {
                (Lexeme::Error, c.len_utf8())
            }
        }
        '`' | '"' | '\'' => {
            let delim = c;
            let lexeme = match delim {
                '`' => Lexeme::Identifier,
                '"' => Lexeme::StringLiteral,
                '\'' => Lexeme::CharacterLiteral,
                _ => unreachable!(),
            };
            let mut len = c.len_utf8();
            let mut escaped = false;
            loop {
                match iter.next() {
                    Some('\r' | '\n') | None => break (Lexeme::Error, len),
                    Some('\\') => {
                        escaped = !escaped;
                        len += c.len_utf8();
                    }
                    Some(c) if c == delim && !escaped => break (lexeme, len + c.len_utf8()),
                    Some(c) => len += c.len_utf8(),
                }
            }
        }
        '!' | '#' | '$' | '%' | '&' | '(' | ')' | '*' | '+' | ',' | '-' | '.' | '/' | ':' | ';'
        | '<' | '=' | '>' | '?' | '@' | '[' | '\\' | ']' | '^' | '{' | '|' | '}' | '~' => {
            (Lexeme::Punctuation, c.len_utf8())
        }
        '\t' | ' ' => {
            let len = c.len_utf8()
                + iter
                    .take_while(|&c| matches!(c, '\t' | ' '))
                    .map(|c| c.len_utf8())
                    .sum::<usize>();
            (Lexeme::Space, len)
        }
        '\n' => (Lexeme::Newline, c.len_utf8()),
        '\r' if iter.next() == Some('\n') => (Lexeme::Newline, 2),
        '\x00'..='\x08' | '\x0B' | '\x0C' | '\x0E'..='\x1F' | '\r' => (Lexeme::Error, c.len_utf8()),
    }
}

impl Syntax {
    pub(crate) fn from_lexeme(lexeme: Lexeme, s: &str) -> Syntax {
        match lexeme {
            Lexeme::Error => Syntax::Error,
            Lexeme::Space => Syntax::Space,
            Lexeme::Newline => Syntax::Newline,
            Lexeme::Comment => Syntax::Comment,
            Lexeme::Identifier => Syntax::Identifier,
            Lexeme::Punctuation => Syntax::from_punct_str(s).unwrap(),
            Lexeme::NumberLiteral => Syntax::Number,
            Lexeme::StringLiteral => Syntax::String,
            Lexeme::CharacterLiteral => Syntax::Character,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        assert_eq!(lex("\r\n"), (Lexeme::Newline, 2));
        assert_eq!(lex("\n"), (Lexeme::Newline, 1));
        assert_eq!(lex("\r "), (Lexeme::Error, 1));
        assert_eq!(lex("  "), (Lexeme::Space, 2));
        assert_eq!(lex("test"), (Lexeme::Identifier, 4));
        assert_eq!(lex("0"), (Lexeme::NumberLiteral, 1));
        assert_eq!(lex("0u32"), (Lexeme::NumberLiteral, 4));
        assert_eq!(lex("'a'"), (Lexeme::CharacterLiteral, 3));
        assert_eq!(lex("'a\n'"), (Lexeme::Error, 2));
        assert_eq!(lex(r#""b""#), (Lexeme::StringLiteral, 3));
        assert_eq!(lex("//\n"), (Lexeme::Comment, 2));
        assert_eq!(lex("//\r\n"), (Lexeme::Comment, 2));
        assert_eq!(lex("//"), (Lexeme::Comment, 2));
    }
}
