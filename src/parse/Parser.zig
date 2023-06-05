const std = @import("std");
const syntax = @import("../syntax.zig");
const lexer = @import("../lex.zig");
const ast = @import("../ast.zig");
const parse = @import("../parse.zig");

const Parser = @This();
const grammar = @import("grammar.zig");

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

    grammar.parseExpr(&parser);

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

    const paren_expr = ast.Expr{ .paren = ast.Expr.Paren.cast(root, untyped_root).? };
    try std.testing.expect(paren_expr.paren.lParen(root) != null);
    try std.testing.expect(paren_expr.paren.expr(root) != null);
    try std.testing.expect(paren_expr.paren.rParen(root) != null);

    const binary_expr = paren_expr.paren.expr(root).?;

    try std.testing.expect(binary_expr.binary.lhs(root) != null);
    try std.testing.expect(binary_expr.binary.rhs(root) != null);
    try std.testing.expect(binary_expr.binary.plus(root) != null);

    const literal_expr = binary_expr.binary.lhs(root).?;
    try std.testing.expect(literal_expr.literal.number(root) != null);
    try std.testing.expectEqualStrings("1", root.tokenText(literal_expr.literal.number(root).?));
}
