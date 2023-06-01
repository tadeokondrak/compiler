pub const TreeTag = enum(u15) {
    invalid,

    decl_fn,

    stmt_block,
    stmt_expr,

    expr_binary,
    expr_ident,
    expr_literal,
    expr_paren,
};

pub const TokenTag = enum(u15) {
    invalid,
    eof,
    space,

    ident,
    number,
    string,

    plus,
    minus,
    star,
    slash,
    percent,

    lt,
    gt,
    eq,

    lt_eq,
    gt_eq,

    lt2,
    gt2,
    eq2,

    dot,
    bang,
    pipe,
    semi,
    caret,
    tilde,
    ampersand,

    l_paren,
    r_paren,
    l_bracket,
    r_bracket,
    l_brace,
    r_brace,

    kw_fn,
};
