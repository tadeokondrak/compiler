const std = @import("std");
const syntax = @import("syntax.zig");
const lexer = @import("lex.zig");
const ast = @import("ast.zig");

const Parser = struct {
    text: []const u8,
    text_pos: usize = 0,
    token_pos: usize = 0,
    tokens: []const lexer.Token,
    builder: syntax.Builder,
    fuel: u8 = 255,

    pub fn deinit(p: *Parser) void {
        p.builder.deinit();
    }

    pub fn nth(p: *Parser, n: usize) syntax.TokenTag {
        p.fuel -|= 1;
        if (p.fuel == 0)
            @panic("out of fuel");
        if (p.token_pos >= p.tokens.len) return .eof;
        return p.tokens[p.token_pos + n].tag;
    }

    pub fn at(p: *Parser, tag: syntax.TokenTag) bool {
        return p.nth(0) == tag;
    }

    pub fn atAny(p: *Parser, comptime tags: []const syntax.TokenTag) bool {
        switch (p.nth(0)) {
            inline else => |tag| {
                return std.mem.indexOfScalar(syntax.TokenTag, tags, tag) != null;
            },
        }
    }

    pub fn eat(p: *Parser, tag: syntax.TokenTag) bool {
        if (!p.at(tag)) return false;
        p.advance();
        return true;
    }

    pub fn bump(p: *Parser, tag: syntax.TokenTag) void {
        std.debug.assert(p.eat(tag));
    }

    pub fn advance(p: *Parser) void {
        const token = p.tokens[p.token_pos];
        p.builder.token(token.tag, p.text[p.text_pos .. p.text_pos + token.len]);
        p.token_pos += 1;
        p.text_pos += token.len;
        p.fuel = 255;
    }

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
            p.parseDecl();
        }
        p.builder.close(m, .file);
    }

    pub fn parseDecl(p: *Parser) void {
        if (p.at(.kw_fn)) {
            p.parseFnDecl();
        } else if (p.at(.kw_struct)) {
            p.parseStructDecl();
        } else {
            const m = p.builder.open();
            while (!p.atAny(&decl_first))
                p.advance();
            p.builder.close(m, .invalid);
        }
    }

    pub fn parseFnDecl(p: *Parser) void {
        const m = p.builder.open();
        p.bump(.kw_fn);
        _ = p.eat(.ident);
        p.parseFnParams();
        p.parseFnReturns();
        p.parseBlockStmt();
        p.builder.close(m, .decl_fn);
    }

    pub fn parseFnParams(p: *Parser) void {
        const m = p.builder.open();
        if (p.eat(.l_paren)) {
            while (p.atAny(&.{ .ident, .colon }) or p.atAny(&expr_first))
                p.parseFnParam();
            _ = p.eat(.r_paren);
        }
        p.builder.close(m, .fn_params);
    }

    pub fn parseFnParam(p: *Parser) void {
        const m = p.builder.open();
        _ = p.eat(.ident);
        _ = p.eat(.colon);
        p.parseExpr();
        p.builder.close(m, .fn_param);
    }

    pub fn parseFnReturns(p: *Parser) void {
        const m = p.builder.open();
        if (p.eat(.l_paren)) {
            while (p.atAny(&.{ .ident, .colon }) or p.atAny(&expr_first))
                p.parseFnReturnNamed();
            _ = p.eat(.r_paren);
        } else {
            p.parseFnReturnAnonymous();
        }
        p.builder.close(m, .fn_returns);
    }

    pub fn parseFnReturnAnonymous(p: *Parser) void {
        const m = p.builder.open();
        p.parseExpr();
        p.builder.close(m, .fn_return);
    }

    pub fn parseFnReturnNamed(p: *Parser) void {
        const m = p.builder.open();
        _ = p.eat(.ident);
        _ = p.eat(.colon);
        p.parseExpr();
        _ = p.eat(.comma);
        p.builder.close(m, .fn_return);
    }

    pub fn parseStructDecl(p: *Parser) void {
        const m = p.builder.open();
        p.bump(.kw_struct);
        _ = p.eat(.ident);
        if (p.eat(.l_brace)) {
            while (p.at(.ident))
                p.parseStructField();
            _ = p.eat(.r_brace);
        }
        p.builder.close(m, .decl_struct);
    }

    pub fn parseStructField(p: *Parser) void {
        const m = p.builder.open();
        _ = p.eat(.ident);
        _ = p.eat(.colon);
        p.parseExpr();
        _ = p.eat(.semi);
        p.builder.close(m, .struct_field);
    }

    pub fn parseBlockStmt(p: *Parser) void {
        const m = p.builder.open();
        _ = p.eat(.l_brace);
        while (!p.atAny(&.{ .r_brace, .eof })) {
            if (p.atAny(&expr_first)) {
                p.parseStmtExpr();
            } else {
                p.advance();
            }
        }
        _ = p.eat(.r_brace);
        p.builder.close(m, .stmt_block);
    }

    pub fn parseStmtExpr(p: *Parser) void {
        std.debug.assert(p.atAny(&expr_first));
        const m = p.builder.open();
        p.parseExpr();
        _ = p.eat(.semi);
        p.builder.close(m, .stmt_expr);
    }

    pub fn parseExpr(p: *Parser) void {
        p.parseExprPrecedence(0);
    }

    pub fn parseExprPrecedence(p: *Parser, left_precedence: u8) void {
        var lhs = lhs: {
            if (unaryPrecedence(p.nth(0))) |right_precedence| {
                const m = p.builder.open();
                p.advance();
                p.parseExprPrecedence(right_precedence);
                p.builder.close(m, .expr_unary);
                break :lhs m;
            }
            break :lhs p.parseExprDelimited() orelse return;
        };
        while (true) {
            const tok = p.nth(0);
            const right_precedence = binopPrecedence(tok) orelse
                break;
            if (right_precedence[0] <= left_precedence)
                break;

            lhs = p.builder.openBefore(lhs);
            p.advance();
            p.parseExprPrecedence(right_precedence[1]);
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

    pub fn parseExprDelimited(p: *Parser) ?syntax.Builder.Mark {
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
            p.parseExpr();
            _ = p.eat(.r_paren);
            p.builder.close(m, .expr_paren);
            return m;
        }

        return null;
    }

    test parseFnDecl {
        try expectSyntaxTree(parseFnDecl,
            \\fn foo() { 1 + 1; }
        ,
            \\decl_fn(
            \\  kw_fn("fn")
            \\  ident("foo")
            \\  l_paren("(")
            \\  r_paren(")")
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
            \\
        );
    }

    test parseBlockStmt {
        try expectSyntaxTree(parseBlockStmt,
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
            \\
        );
    }

    test parseStmtExpr {
        try expectSyntaxTree(parseStmtExpr,
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
            \\
        );
    }

    test parseExpr {
        try expectSyntaxTree(parseExpr,
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
            \\
        );
    }
};

pub fn parseFile(allocator: std.mem.Allocator, src: []const u8) error{OutOfMemory}!syntax.Root {
    var tokens = std.ArrayList(lexer.Token).init(allocator);
    defer tokens.deinit();

    var text = std.ArrayList(u8).init(allocator);
    defer text.deinit();

    var l = lexer.Lexer{ .text = src };
    var pos: usize = 0;
    while (l.next()) |token| {
        if (token.tag != .space) {
            try tokens.append(token);
            try text.appendSlice(src[pos .. pos + token.len]);
        }
        pos += token.len;
    }

    var parser = Parser{
        .text = text.items,
        .tokens = tokens.items,
        .builder = syntax.Builder{
            .allocator = allocator,
        },
    };
    defer parser.deinit();

    parser.parseFile();

    return parser.builder.build(allocator);
}

fn expectSyntaxTree(comptime parseFunc: fn (*Parser) void, src: []const u8, expect: []const u8) !void {
    var tokens = std.ArrayList(lexer.Token).init(std.testing.allocator);
    defer tokens.deinit();

    var text = std.ArrayList(u8).init(std.testing.allocator);
    defer text.deinit();

    var l = lexer.Lexer{ .text = src };
    var pos: usize = 0;
    while (l.next()) |token| {
        if (token.tag != .space) {
            try tokens.append(token);
            try text.appendSlice(src[pos .. pos + token.len]);
        }
        pos += token.len;
    }

    var parser = Parser{
        .text = text.items,
        .tokens = tokens.items,
        .builder = syntax.Builder{
            .allocator = std.testing.allocator,
        },
    };
    defer parser.deinit();

    parseFunc(&parser);

    var events_text = std.ArrayList(u8).init(std.testing.allocator);
    defer events_text.deinit();

    var root = try parser.builder.build(std.testing.allocator);
    defer root.deinit(std.testing.allocator);

    const tree_text = try std.fmt.allocPrint(std.testing.allocator, "{}", .{root});
    defer std.testing.allocator.free(tree_text);
    try std.testing.expectEqualStrings(expect, tree_text);
}

test Parser {
    const src = "(1+2)";

    var tokens = std.ArrayList(lexer.Token).init(std.testing.allocator);
    defer tokens.deinit();

    var l = lexer.Lexer{ .text = src };
    while (l.next()) |token|
        try tokens.append(token);

    try std.testing.expectEqualSlices(lexer.Token, &[_]lexer.Token{
        .{ .tag = .l_paren, .len = 1 },
        .{ .tag = .number, .len = 1 },
        .{ .tag = .plus, .len = 1 },
        .{ .tag = .number, .len = 1 },
        .{ .tag = .r_paren, .len = 1 },
    }, tokens.items);

    var parser = Parser{
        .text = src,
        .tokens = tokens.items,
        .builder = syntax.Builder{
            .allocator = std.testing.allocator,
        },
    };
    defer parser.deinit();

    parser.parseExpr();

    var events_text = std.ArrayList(u8).init(std.testing.allocator);
    defer events_text.deinit();

    var indent: usize = 0;
    for (parser.builder.events.items) |event| {
        switch (event) {
            .open => |open| {
                try events_text.writer().writeByteNTimes(' ', indent);
                try events_text.writer().print("open({s})\n", .{@tagName(open.tag)});
                indent += 2;
            },
            .close => {
                indent -= 2;
                try events_text.writer().writeByteNTimes(' ', indent);
                try events_text.writer().print("close\n", .{});
            },
            .token => |token| {
                try events_text.writer().writeByteNTimes(' ', indent);
                try events_text.writer().print("token({s}, \"{}\")\n", .{ @tagName(token.tag), std.zig.fmtEscapes(token.text) });
            },
        }
    }
    try std.testing.expectEqualStrings(
        \\open(expr_paren)
        \\  token(l_paren, "(")
        \\  open(expr_binary)
        \\    open(expr_literal)
        \\      token(number, "1")
        \\    close
        \\    token(plus, "+")
        \\    open(expr_literal)
        \\      token(number, "2")
        \\    close
        \\  close
        \\  token(r_paren, ")")
        \\close
        \\
    , events_text.items);

    var root = try parser.builder.build(std.testing.allocator);
    defer root.deinit(std.testing.allocator);

    const tree_text = try std.fmt.allocPrint(std.testing.allocator, "{}", .{root});
    defer std.testing.allocator.free(tree_text);
    try std.testing.expectEqualStrings(
        \\expr_paren(
        \\  l_paren("(")
        \\  expr_binary(
        \\    expr_literal(
        \\      number("1")
        \\    )
        \\    plus("+")
        \\    expr_literal(
        \\      number("2")
        \\    )
        \\  )
        \\  r_paren(")")
        \\)
        \\
    , tree_text);

    const untyped_root = @intToEnum(syntax.Tree, 0);

    const paren_expr = ast.Expr{ .paren = ast.ExprParen.cast(&root, untyped_root).? };
    try std.testing.expect(paren_expr.paren.l_paren(&root) != null);
    try std.testing.expect(paren_expr.paren.expr(&root) != null);
    try std.testing.expect(paren_expr.paren.r_paren(&root) != null);

    const binary_expr = paren_expr.paren.expr(&root).?;

    try std.testing.expect(binary_expr.binary.lhs(&root) != null);
    try std.testing.expect(binary_expr.binary.rhs(&root) != null);
    try std.testing.expect(binary_expr.binary.plus(&root) != null);

    const literal_expr = binary_expr.binary.lhs(&root).?;
    try std.testing.expect(literal_expr.literal.number(&root) != null);
    try std.testing.expectEqualStrings("1", root.tokenText(literal_expr.literal.number(&root).?));
}
