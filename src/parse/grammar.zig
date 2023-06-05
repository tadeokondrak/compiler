const std = @import("std");
const syntax = @import("../syntax.zig");
const lexer = @import("../lex.zig");
const ast = @import("../ast.zig");
const parse = @import("../parse.zig");

const Parser = @import("Parser.zig");

const decl_first = [_]syntax.TokenTag{
    .kw_fn,
    .kw_struct,
};

const expr_first = [_]syntax.TokenTag{
    .number,
    .l_paren,
    .kw_return,
};

pub fn parseFile(p: *Parser) void {
    const m = p.builder.open();
    while (!p.at(.eof)) {
        parseDecl(p);
    }
    p.builder.close(m, .file);
}

fn parseDecl(p: *Parser) void {
    if (p.at(.kw_fn)) {
        parseFnDecl(p);
    } else if (p.at(.kw_struct)) {
        parseStructDecl(p);
    } else {
        const m = p.builder.open();
        while (!p.atAny(&decl_first))
            p.advance();
        p.builder.close(m, .invalid);
    }
}

fn parseFnDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_fn);
    _ = p.eat(.ident);
    parseFnParams(p);
    parseFnReturns(p);
    parseBlockStmt(p);
    p.builder.close(m, .decl_fn);
}

fn parseFnParams(p: *Parser) void {
    const m = p.builder.open();
    if (p.eat(.l_paren)) {
        while (p.atAny(&.{ .ident, .colon }) or p.atAny(&expr_first))
            parseFnParam(p);
        _ = p.eat(.r_paren);
    }
    p.builder.close(m, .fn_params);
}

fn parseFnParam(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.ident);
    _ = p.eat(.colon);
    parseExpr(p);
    p.builder.close(m, .fn_param);
}

fn parseFnReturns(p: *Parser) void {
    const m = p.builder.open();
    if (p.eat(.l_paren)) {
        while (p.atAny(&.{ .ident, .colon }) or p.atAny(&expr_first))
            parseFnReturnNamed(p);
        _ = p.eat(.r_paren);
    } else {
        parseFnReturnAnonymous(p);
    }
    p.builder.close(m, .fn_returns);
}

fn parseFnReturnAnonymous(p: *Parser) void {
    const m = p.builder.open();
    parseExpr(p);
    p.builder.close(m, .fn_return);
}

fn parseFnReturnNamed(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.ident);
    _ = p.eat(.colon);
    parseExpr(p);
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
    _ = p.eat(.colon);
    parseExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .struct_field);
}

fn parseBlockStmt(p: *Parser) void {
    const m = p.builder.open();
    _ = p.eat(.l_brace);
    while (!p.atAny(&.{ .r_brace, .eof })) {
        if (p.atAny(&expr_first)) {
            parseStmtExpr(p);
        } else {
            p.advance();
        }
    }
    _ = p.eat(.r_brace);
    p.builder.close(m, .stmt_block);
}

fn parseStmtExpr(p: *Parser) void {
    std.debug.assert(p.atAny(&expr_first));
    const m = p.builder.open();
    parseExpr(p);
    _ = p.eat(.semi);
    p.builder.close(m, .stmt_expr);
}

pub fn parseExpr(p: *Parser) void {
    parseExprPrecedence(p, 0);
}

fn parseExprPrecedence(p: *Parser, left_precedence: u8) void {
    var lhs = lhs: {
        if (unaryPrecedence(p.nth(0))) |right_precedence| {
            const m = p.builder.open();
            p.advance();
            parseExprPrecedence(p, right_precedence);
            p.builder.close(m, .expr_unary);
            break :lhs m;
        }
        break :lhs parseExprDelimited(p) orelse return;
    };
    while (true) {
        const tok = p.nth(0);
        const right_precedence = binopPrecedence(tok) orelse
            break;
        if (right_precedence[0] <= left_precedence)
            break;

        lhs = p.builder.openBefore(lhs);
        p.advance();
        parseExprPrecedence(p, right_precedence[1]);
        p.builder.close(lhs, .expr_binary);
    }
}

fn unaryPrecedence(tag: syntax.TokenTag) ?u8 {
    return switch (tag) {
        .kw_return => 1,
        else => null,
    };
}

fn binopPrecedence(tag: syntax.TokenTag) ?[2]u8 {
    return switch (tag) {
        // .eof is zero, but we don't return it here
        .lt, .gt, .eq2 => .{ 2, 2 },
        .plus, .minus => .{ 3, 4 },
        .star, .slash, .percent => .{ 5, 6 },
        else => null,
    };
}

fn parseExprDelimited(p: *Parser) ?syntax.Builder.Mark {
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

test parseStmtExpr {
    try parse.expectSyntaxTree(parseStmtExpr,
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
