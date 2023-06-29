const std = @import("std");
const syntax = @import("../syntax.zig");
const lex = @import("lex.zig");
const parse = @import("../parse.zig");

const ast = syntax.ast;

const Parser = @This();
const grammar = @import("grammar.zig");

token_pos: usize = 0,
tokens: []const syntax.pure.Token.Tag,
builder: syntax.pure.Builder,
fuel: u8 = 255,

pub fn deinit(p: *Parser) void {
    p.builder.deinit();
}

pub fn nth(p: *Parser, n: usize) syntax.pure.Token.Tag {
    p.fuel -|= 1;
    if (p.fuel == 0)
        @panic("out of fuel");
    if (p.token_pos >= p.tokens.len) return .eof;
    return p.tokens[p.token_pos + n];
}

pub fn at(p: *Parser, tag: syntax.pure.Token.Tag) bool {
    return p.nth(0) == tag;
}

pub fn atAny(p: *Parser, comptime tags: []const syntax.pure.Token.Tag) bool {
    return std.mem.indexOfScalar(syntax.pure.Token.Tag, tags, p.nth(0)) != null;
}

pub fn eat(p: *Parser, tag: syntax.pure.Token.Tag) bool {
    if (!p.at(tag)) return false;
    p.advance();
    return true;
}

pub fn bump(p: *Parser, tag: syntax.pure.Token.Tag) void {
    std.debug.assert(p.eat(tag));
}

pub fn advance(p: *Parser) void {
    const token = p.tokens[p.token_pos];
    p.builder.token(token);
    p.token_pos += 1;
    p.fuel = 255;
}
