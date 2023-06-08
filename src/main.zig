const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const ast = @import("ast.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");
const Context = @import("Context.zig");

comptime {
    _ = syntax;
    _ = lex;
    _ = ast;
    _ = parse;
    _ = ir;
    _ = Context;
}

pub fn main() !void {
    const src =
        \\struct Struct {
        \\    field1 u32;
        \\    field2 u32;
        \\}
        \\fn main(x u32) {
        \\    return 1 + 1 + 2 + f();
        \\}
    ;

    std.debug.print("source: '{s}'\n", .{src});
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    var ctx = try Context.init(gpa.allocator(), src);
    defer ctx.deinit();
    try ctx.analyzeDecls();
}
