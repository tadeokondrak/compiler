#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum Syntax {
    Eof,
    Error,
    Comment,
    Space,
    Newline,
    Number,
    String,
    Character,
    Identifier,
    ExclamationMark,
    ExclamationMarkEqualsSign,
    NumberSign,
    DollarSign,
    PercentSign,
    PercentSignEqualsSign,
    Ampersand,
    AmpersandEqualsSign,
    LeftParenthesis,
    RightParenthesis,
    Asterisk,
    AsteriskEqualsSign,
    PlusSign,
    PlusSignEqualsSign,
    Comma,
    HyphenMinus,
    HyphenMinusEqualsSign,
    FullStop,
    Solidus,
    SolidusEqualsSign,
    Colon,
    Semicolon,
    LessThanSign,
    LessThanSignLessThanSign,
    LessThanSignLessThanSignEqualsSign,
    LessThanSignEqualsSign,
    EqualsSign,
    EqualsSignEqualsSign,
    GreaterThanSign,
    GreaterThanSignEqualsSign,
    GreaterThanSignGreaterThanSign,
    GreaterThanSignGreaterThanSignEqualsSign,
    QuestionMark,
    CommercialAt,
    LeftSquareBracket,
    ReverseSolidus,
    RightSquareBracket,
    CircumflexAccent,
    CircumflexAccentEqualsSign,
    LowLine,
    LeftCurlyBracket,
    VerticalLine,
    VerticalLineEqualsSign,
    RightCurlyBracket,
    Tilde,
    AndKeyword,
    BreakKeyword,
    ConstKeyword,
    ContinueKeyword,
    DerefKeyword,
    ElseKeyword,
    EnumKeyword,
    FnKeyword,
    IfKeyword,
    LetKeyword,
    LoopKeyword,
    OrKeyword,
    PtrKeyword,
    RefKeyword,
    ReturnKeyword,
    SliceKeyword,
    StructKeyword,
    UnionKeyword,
    VariantKeyword,
    WhileKeyword,
    File,
    ItemStmt,
    ExprStmt,
    LetStmt,
    FnItem,
    EnumItem,
    RecordItem,
    ConstItem,
    Parameter,
    BlockExpr,
    Variant,
    Member,
    ParenExpr,
    NameExpr,
    LiteralExpr,
    IfExpr,
    LoopExpr,
    WhileExpr,
    UnaryExpr,
    BinaryExpr,
    BreakExpr,
    ReturnExpr,
    ContinueExpr,
    CallExpr,
    IndexExpr,
    FieldExpr,
    Argument,
    ParenType,
    NameType,
    SliceType,
    PointerType,
}
impl Syntax {
    pub(crate) const LAST: Syntax = Syntax::PointerType;
    pub(crate) fn from_punct_str(s: &str) -> Option<Syntax> {
        match s {
            "!" => Some(Syntax::ExclamationMark),
            "!=" => Some(Syntax::ExclamationMarkEqualsSign),
            "#" => Some(Syntax::NumberSign),
            "$" => Some(Syntax::DollarSign),
            "%" => Some(Syntax::PercentSign),
            "%=" => Some(Syntax::PercentSignEqualsSign),
            "&" => Some(Syntax::Ampersand),
            "&=" => Some(Syntax::AmpersandEqualsSign),
            "(" => Some(Syntax::LeftParenthesis),
            ")" => Some(Syntax::RightParenthesis),
            "*" => Some(Syntax::Asterisk),
            "*=" => Some(Syntax::AsteriskEqualsSign),
            "+" => Some(Syntax::PlusSign),
            "+=" => Some(Syntax::PlusSignEqualsSign),
            "," => Some(Syntax::Comma),
            "-" => Some(Syntax::HyphenMinus),
            "-=" => Some(Syntax::HyphenMinusEqualsSign),
            "." => Some(Syntax::FullStop),
            "/" => Some(Syntax::Solidus),
            "/=" => Some(Syntax::SolidusEqualsSign),
            ":" => Some(Syntax::Colon),
            ";" => Some(Syntax::Semicolon),
            "<" => Some(Syntax::LessThanSign),
            "<<" => Some(Syntax::LessThanSignLessThanSign),
            "<<=" => Some(Syntax::LessThanSignLessThanSignEqualsSign),
            "<=" => Some(Syntax::LessThanSignEqualsSign),
            "=" => Some(Syntax::EqualsSign),
            "==" => Some(Syntax::EqualsSignEqualsSign),
            ">" => Some(Syntax::GreaterThanSign),
            ">=" => Some(Syntax::GreaterThanSignEqualsSign),
            ">>" => Some(Syntax::GreaterThanSignGreaterThanSign),
            ">>=" => Some(Syntax::GreaterThanSignGreaterThanSignEqualsSign),
            "?" => Some(Syntax::QuestionMark),
            "@" => Some(Syntax::CommercialAt),
            "[" => Some(Syntax::LeftSquareBracket),
            "\\" => Some(Syntax::ReverseSolidus),
            "]" => Some(Syntax::RightSquareBracket),
            "^" => Some(Syntax::CircumflexAccent),
            "^=" => Some(Syntax::CircumflexAccentEqualsSign),
            "_" => Some(Syntax::LowLine),
            "{" => Some(Syntax::LeftCurlyBracket),
            "|" => Some(Syntax::VerticalLine),
            "|=" => Some(Syntax::VerticalLineEqualsSign),
            "}" => Some(Syntax::RightCurlyBracket),
            "~" => Some(Syntax::Tilde),
            _ => None,
        }
    }
    pub(crate) fn from_keyword_str(s: &str) -> Option<Syntax> {
        match s {
            "and" => Some(Syntax::AndKeyword),
            "break" => Some(Syntax::BreakKeyword),
            "const" => Some(Syntax::ConstKeyword),
            "continue" => Some(Syntax::ContinueKeyword),
            "deref" => Some(Syntax::DerefKeyword),
            "else" => Some(Syntax::ElseKeyword),
            "enum" => Some(Syntax::EnumKeyword),
            "fn" => Some(Syntax::FnKeyword),
            "if" => Some(Syntax::IfKeyword),
            "let" => Some(Syntax::LetKeyword),
            "loop" => Some(Syntax::LoopKeyword),
            "or" => Some(Syntax::OrKeyword),
            "ptr" => Some(Syntax::PtrKeyword),
            "ref" => Some(Syntax::RefKeyword),
            "return" => Some(Syntax::ReturnKeyword),
            "slice" => Some(Syntax::SliceKeyword),
            "struct" => Some(Syntax::StructKeyword),
            "union" => Some(Syntax::UnionKeyword),
            "variant" => Some(Syntax::VariantKeyword),
            "while" => Some(Syntax::WhileKeyword),
            _ => None,
        }
    }
    #[rustfmt::skip]
    pub(crate) fn decompose_2(self) -> Option<[Syntax; 2usize]> {
        match self {
            Syntax::ExclamationMarkEqualsSign => {
                Some([Syntax::ExclamationMark, Syntax::EqualsSign])
            }
            Syntax::PercentSignEqualsSign => {
                Some([Syntax::PercentSign, Syntax::EqualsSign])
            }
            Syntax::AmpersandEqualsSign => Some([Syntax::Ampersand, Syntax::EqualsSign]),
            Syntax::AsteriskEqualsSign => Some([Syntax::Asterisk, Syntax::EqualsSign]),
            Syntax::PlusSignEqualsSign => Some([Syntax::PlusSign, Syntax::EqualsSign]),
            Syntax::HyphenMinusEqualsSign => {
                Some([Syntax::HyphenMinus, Syntax::EqualsSign])
            }
            Syntax::SolidusEqualsSign => Some([Syntax::Solidus, Syntax::EqualsSign]),
            Syntax::LessThanSignLessThanSign => {
                Some([Syntax::LessThanSign, Syntax::LessThanSign])
            }
            Syntax::LessThanSignEqualsSign => {
                Some([Syntax::LessThanSign, Syntax::EqualsSign])
            }
            Syntax::EqualsSignEqualsSign => {
                Some([Syntax::EqualsSign, Syntax::EqualsSign])
            }
            Syntax::GreaterThanSignEqualsSign => {
                Some([Syntax::GreaterThanSign, Syntax::EqualsSign])
            }
            Syntax::GreaterThanSignGreaterThanSign => {
                Some([Syntax::GreaterThanSign, Syntax::GreaterThanSign])
            }
            Syntax::CircumflexAccentEqualsSign => {
                Some([Syntax::CircumflexAccent, Syntax::EqualsSign])
            }
            Syntax::VerticalLineEqualsSign => {
                Some([Syntax::VerticalLine, Syntax::EqualsSign])
            }
            _ => None,
        }
    }
    #[rustfmt::skip]
    pub(crate) fn decompose_3(self) -> Option<[Syntax; 3usize]> {
        match self {
            Syntax::LessThanSignLessThanSignEqualsSign => {
                Some([Syntax::LessThanSign, Syntax::LessThanSign, Syntax::EqualsSign])
            }
            Syntax::GreaterThanSignGreaterThanSignEqualsSign => {
                Some([
                    Syntax::GreaterThanSign,
                    Syntax::GreaterThanSign,
                    Syntax::EqualsSign,
                ])
            }
            _ => None,
        }
    }
}
