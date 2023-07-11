const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");

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
        .lt, .lt_eq, .gt, .gt_eq, .eq2, .bang_eq => .{ 2, 2 },
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

fn typePrefixPrecedence(tag: syntax.pure.Token.Tag) ?u8 {
    return switch (tag) {
        .star => 1,
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
    .ident,
};

const type_expr_first = [_]syntax.pure.Token.Tag{
    .star,
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
    p.expect(.ident);
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
            if (!parseFnParam(p))
                break;
    }
    p.expect(.r_paren);
    p.builder.close(m, .fn_params);
}

fn parseFnParam(p: *Parser) bool {
    const m = p.builder.open();
    p.expect(.ident);
    parseTypeExpr(p);
    const comma = p.eat(.comma);
    p.builder.close(m, .fn_param);
    return comma;
}

fn parseFnReturns(p: *Parser) void {
    const m = p.builder.open();
    if (p.eat(.l_paren)) {
        while (p.at(.ident) or p.atAny(&expr_first))
            parseFnReturnNamed(p);
        p.expect(.r_paren);
    } else if (p.atAny(&type_expr_first)) {
        parseFnReturnAnonymous(p);
    }
    p.builder.close(m, .fn_returns);
}

fn parseFnReturnNamed(p: *Parser) void {
    const m = p.builder.open();
    p.expect(.ident);
    parseTypeExpr(p);
    _ = p.eat(.comma);
    p.builder.close(m, .fn_return);
}

fn parseFnReturnAnonymous(p: *Parser) void {
    const m = p.builder.open();
    parseTypeExpr(p);
    p.builder.close(m, .fn_return);
}

fn parseStructDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_struct);
    p.expect(.ident);
    if (p.eat(.l_brace)) {
        while (p.at(.ident))
            parseStructField(p);
        p.expect(.r_brace);
    }
    p.builder.close(m, .decl_struct);
}

fn parseStructField(p: *Parser) void {
    const m = p.builder.open();
    p.expect(.ident);
    parseTypeExpr(p);
    p.expect(.semi);
    p.builder.close(m, .struct_field);
}

fn parseConstDecl(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_const);
    p.expect(.ident);
    parseTypeExpr(p);
    p.expect(.eq);
    parseExpr(p);
    p.expect(.semi);
    p.builder.close(m, .decl_const);
}

fn parseStmt(p: *Parser) void {
    if (p.atAny(&expr_first)) {
        parseExprStmt(p);
        return;
    }

    switch (p.nth(0)) {
        .l_brace => parseBlockStmt(p),
        .kw_return => parseReturnStmt(p),
        .kw_continue => parseContinueStmt(p),
        .kw_break => parseBreakStmt(p),
        .kw_if => parseIfStmt(p),
        .kw_loop => parseLoopStmt(p),
        .kw_while => parseWhileStmt(p),
        else => {
            @panic("TODO");
        },
    }
}

fn parseBlockStmt(p: *Parser) void {
    const m = p.builder.open();
    p.expect(.l_brace);
    while (!p.atAny(&.{ .r_brace, .eof })) {
        if (p.atAny(&expr_first)) {
            parseExprStmt(p);
        } else {
            parseStmt(p);
            //p.advance();
        }
    }
    p.expect(.r_brace);
    p.builder.close(m, .stmt_block);
}

fn parseExprStmt(p: *Parser) void {
    std.debug.assert(p.atAny(&expr_first));
    const m = p.builder.open();
    parseExpr(p);
    p.expect(.semi);
    p.builder.close(m, .stmt_expr);
}

fn parseReturnStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_return);
    parseExpr(p);
    p.expect(.semi);
    p.builder.close(m, .stmt_return);
}

fn parseContinueStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_continue);
    p.expect(.semi);
    p.builder.close(m, .stmt_continue);
}

fn parseBreakStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_break);
    p.expect(.semi);
    p.builder.close(m, .stmt_break);
}

fn parseIfStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_if);
    parseExpr(p);
    parseBlockStmt(p);
    if (p.eat(.kw_else))
        parseBlockStmt(p);
    p.builder.close(m, .stmt_if);
}

fn parseLoopStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_loop);
    parseBlockStmt(p);
    p.builder.close(m, .stmt_loop);
}

fn parseWhileStmt(p: *Parser) void {
    const m = p.builder.open();
    p.bump(.kw_while);
    parseExpr(p);
    parseBlockStmt(p);
    p.builder.close(m, .stmt_while);
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
                const args = p.builder.open();
                while (!p.at(.r_paren) and !p.at(.eof)) {
                    const arg = p.builder.open();
                    parseExpr(p);
                    const comma = p.eat(.comma);
                    p.builder.close(arg, .call_arg);
                    if (!comma)
                        break;
                }
                p.expect(.r_paren);
                p.builder.close(args, .call_args);
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
        p.expect(.r_paren);
        p.builder.close(m, .expr_paren);
        return m;
    }

    return null;
}

fn parseTypeExpr(p: *Parser) void {
    parseTypeExprPrecedence(p, 0);
}

fn parseTypeExprPrecedence(p: *Parser, left_precedence: u8) void {
    _ = left_precedence;
    if (typePrefixPrecedence(p.nth(0))) |prec| {
        const m = p.builder.open();
        p.advance();
        parseTypeExprPrecedence(p, prec);
        p.builder.close(m, .type_expr_unary);
        return;
    }
    _ = parseTypeExprDelimited(p);
    return;
}

fn parseTypeExprDelimited(p: *Parser) ?syntax.pure.Builder.Mark {
    if (p.at(.ident)) {
        const m = p.builder.open();
        p.bump(.ident);
        p.builder.close(m, .type_expr_ident);
        return m;
    }

    return null;
}
