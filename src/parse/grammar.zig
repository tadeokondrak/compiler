const std = @import("std");
const syntax = @import("../syntax.zig");
const parse = @import("../parse.zig");

const Parser = @import("Parser.zig");

fn prefixPrecedence(tag: syntax.pure.Token.Tag) ?u8 {
    return switch (tag) {
        .plus, .minus => 1,
        else => null,
    };
}

fn infixPrecedence(tag: syntax.pure.Token.Tag) ?[2]u8 {
    return switch (tag) {
        // .eof is zero, but we don't return it here
        .lt, .gt, .eq2 => .{ 2, 2 },
        .plus, .minus => .{ 3, 4 },
        .star, .slash, .percent => .{ 5, 6 },
        else => null,
    };
}

fn postfixPrecedence(tag: syntax.pure.Token.Tag) ?u8 {
    return switch (tag) {
        .l_paren => 7,
        else => null,
    };
}

const decl_first = [_]syntax.pure.Token.Tag{
    .kw_fn,
    .kw_struct,
    .kw_const,
};

const expr_first = [_]syntax.pure.Token.Tag{
    .number,
    .l_paren,
};

const type_expr_first = [_]syntax.pure.Token.Tag{
    .ident,
};

pub fn parseFile(p: *Parser) void {
    const m = p.builder.open();
    while (!p.at(.eof)) {
        if (p.atAny(&decl_first)) {
            parseDecl(p);
        } else {
            const invalid_marker = p.builder.open();
            while (!p.atAny(&decl_first))
                p.advance();
            p.builder.close(invalid_marker, .invalid);
        }
    }
    p.builder.close(m, .file);
}

fn parseDecl(p: *Parser) void {
    std.debug.assert(p.atAny(&decl_first));
    switch (p.nth(0)) {
        .kw_fn => parseFnDecl(p),
        .kw_struct => parseStructDecl(p),
        .kw_const => parseConstDecl(p),
        else => unreachable,
    }
}

fn parseFnDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_fn);
    _ = p.eat(.ident);
    if (p.at(.l_paren))
        parseFnParams(p);
    if (p.at(.l_paren) or p.atAny(&type_expr_first))
        parseFnReturns(p);
    parseBlockStmt(p);
    p.builder.close(m, .decl_fn);
}

fn parseFnParams(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.l_paren);
    while (!p.at(.r_paren) and !p.at(.eof)) {
        if (p.at(.ident) or p.atAny(&type_expr_first))
            parseFnParam(p)
        else
            break;
    }
    _ = p.eat(.r_paren);
    p.builder.close(m, .fn_params);
}

fn parseFnParam(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.ident);
    parseTypeExpr(p);
    _ = p.eat(.comma);
    p.builder.close(m, .fn_param);
}

fn parseFnReturns(p: *Parser) void {
    const m = p.builder.open();
    if (p.eat(.l_paren)) {
        while (p.at(.ident) or p.atAny(&expr_first))
            parseFnReturnNamed(p);
        _ = p.eat(.r_paren);
    }
    p.builder.close(m, .fn_returns);
}

fn parseFnReturnNamed(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.ident);
    parseTypeExpr(p);
    _ = p.eat(.comma);
    p.builder.close(m, .fn_return);
}

fn parseStructDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_struct);
    _ = p.eat(.ident);
    if (p.eat(.l_brace)) {
        while (p.at(.ident))
            parseStructField(p);
        _ = p.eat(.r_brace);
    }
    p.builder.close(m, .decl_struct);
}

fn parseStructField(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.ident);
    parseTypeExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .struct_field);
}

fn parseConstDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_const);
    _ = p.eat(.ident);
    parseTypeExpr(p);
    _ = p.eat(.eq);
    parseExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .decl_const);
}

fn parseStmt(p: *Parser) void {
    if (p.at(.l_brace)) {
        parseBlockStmt(p);
    } else if (p.atAny(&expr_first)) {
        parseExprStmt(p);
    } else if (p.at(.kw_return)) {
        parseReturnStmt(p);
    } else {
        @panic("TODO");
        //p.advance();
    }
}

fn parseBlockStmt(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.l_brace);
    while (!p.atAny(&.{ .r_brace, .eof })) {
        if (p.atAny(&expr_first)) {
            parseExprStmt(p);
        } else {
            parseStmt(p);
            //p.advance();
        }
    }
    _ = p.eat(.r_brace);
    p.builder.close(m, .stmt_block);
}

fn parseExprStmt(p: *Parser) void {
    std.debug.assert(p.atAny(&expr_first));
    const m = p.builder.open();
    parseExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .stmt_expr);
}

fn parseReturnStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_return);
    parseExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .stmt_return);
}

pub fn parseExpr(p: *Parser) void {
    parseExprPrecedence(p, 0);
}

fn parseExprPrecedence(p: *Parser, left_precedence: u8) void {
    var lhs = lhs: {
        if (prefixPrecedence(p.nth(0))) |prec| {
            const m = p.builder.open();
            p.advance();
            parseExprPrecedence(p, prec);
            p.builder.close(m, .expr_unary);
            break :lhs m;
        }
        break :lhs parseExprDelimited(p) orelse return;
    };
    while (true) {
        const tok = p.nth(0);

        if (postfixPrecedence(tok)) |prec| {
            if (prec <= left_precedence)
                break;

            lhs = p.builder.openBefore(lhs);
            p.advance();
            if (tok == .l_paren) {
                parseExpr(p);
                _ = p.eat(.r_paren);
                p.builder.close(lhs, .expr_call);
            } else {
                p.builder.close(lhs, .expr_unary);
            }

            continue;
        }

        if (infixPrecedence(tok)) |prec| {
            if (prec[0] <= left_precedence)
                break;

            lhs = p.builder.openBefore(lhs);
            p.advance();
            parseExprPrecedence(p, prec[1]);
            p.builder.close(lhs, .expr_binary);

            continue;
        }

        break;
    }
}

fn parseExprDelimited(p: *Parser) ?syntax.pure.Builder.Mark {
    if (p.at(.number)) {
        const m = p.builder.open();
        p.bump(.number);
        p.builder.close(m, .expr_literal);
        return m;
    }

    if (p.at(.ident)) {
        const m = p.builder.open();
        p.bump(.ident);
        p.builder.close(m, .expr_ident);
        return m;
    }

    if (p.at(.l_paren)) {
        const m = p.builder.open();
        p.bump(.l_paren);
        parseExpr(p);
        _ = p.eat(.r_paren);
        p.builder.close(m, .expr_paren);
        return m;
    }

    return null;
}

pub fn parseTypeExpr(p: *Parser) void {
    if (p.at(.ident)) {
        const m = p.builder.open();
        p.bump(.ident);
        p.builder.close(m, .type_expr_ident);
        return;
    }
}

test parseFnDecl {
    try parse.expectSyntaxTree(parseFnDecl,
        \\fn foo() { 1 + 1; }
    ,
        \\decl_fn(
        \\  kw_fn("fn")
        \\  ident("foo")
        \\  fn_params(
        \\    l_paren("(")
        \\    r_paren(")")
        \\  )
        \\  fn_returns(
        \\    fn_return(
        \\    )
        \\  )
        \\  stmt_block(
        \\    l_brace("{")
        \\    stmt_expr(
        \\      expr_binary(
        \\        expr_literal(
        \\          number("1")
        \\        )
        \\        plus("+")
        \\        expr_literal(
        \\          number("1")
        \\        )
        \\      )
        \\      semi(";")
        \\    )
        \\    r_brace("}")
        \\  )
        \\)
    );
}

test parseBlockStmt {
    try parse.expectSyntaxTree(parseBlockStmt,
        \\{ 1 + 2; }
    ,
        \\stmt_block(
        \\  l_brace("{")
        \\  stmt_expr(
        \\    expr_binary(
        \\      expr_literal(
        \\        number("1")
        \\      )
        \\      plus("+")
        \\      expr_literal(
        \\        number("2")
        \\      )
        \\    )
        \\    semi(";")
        \\  )
        \\  r_brace("}")
        \\)
    );
}

test parseExprStmt {
    try parse.expectSyntaxTree(parseExprStmt,
        \\1 + 2;
    ,
        \\stmt_expr(
        \\  expr_binary(
        \\    expr_literal(
        \\      number("1")
        \\    )
        \\    plus("+")
        \\    expr_literal(
        \\      number("2")
        \\    )
        \\  )
        \\  semi(";")
        \\)
    );
}

test parseExpr {
    try parse.expectSyntaxTree(parseExpr,
        \\1 + 2 * 3 / 4
    ,
        \\expr_binary(
        \\  expr_literal(
        \\    number("1")
        \\  )
        \\  plus("+")
        \\  expr_binary(
        \\    expr_binary(
        \\      expr_literal(
        \\        number("2")
        \\      )
        \\      star("*")
        \\      expr_literal(
        \\        number("3")
        \\      )
        \\    )
        \\    slash("/")
        \\    expr_literal(
        \\      number("4")
        \\    )
        \\  )
        \\)
    );
}
