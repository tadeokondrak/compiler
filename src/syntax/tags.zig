pub const TreeTag = enum(u15) {
    invalid,

    file,

    decl_fn,
    decl_const,
    decl_struct,

    expr_unary,
    expr_binary,
    expr_ident,
    expr_literal,
    expr_paren,
    expr_call,

    stmt_block,
    stmt_expr,
    stmt_return,

    fn_params,
    fn_param,
    fn_returns,
    fn_return,

    struct_field,
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
    colon,
    comma,
    ampersand,

    l_paren,
    r_paren,
    l_bracket,
    r_bracket,
    l_brace,
    r_brace,

    kw_fn,
    kw_return,
    kw_struct,
};
