const std = @import("std");
const syntax = @import("syntax.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");
const Context = @import("Context.zig");

comptime {
    _ = syntax;
    _ = parse;
    _ = ir;
    _ = Context;
}

pub fn main() !void {
    const src =
        \\const num u32 = 1;
        \\const ptr *u64 = num;
        \\struct Struct {
        \\    field1 u32;
        \\    field2 *u32;
        \\}
        \\struct Node {
        \\    next *Node;
        \\}
        \\struct Other {
        \\    field1 Struct;
        \\}
        \\fn add(a u32, b u32) (ret u32) {
        \\    return a + b;
        \\}
        \\fn fib(n u32) (ret u32) {
        \\    if n <= 1 {
        \\        return 1;
        \\    }
        \\    return add(fib(n - 1), fib(n - 2));
        \\}
    ;

    var gpa: std.heap.GeneralPurposeAllocator(.{ .stack_trace_frames = 32 }) = .{};
    defer _ = gpa.deinit();
    var ctx = try Context.init(gpa.allocator(), src);
    defer ctx.deinit();
    //std.debug.print("syntax: {}\n", .{ctx.root});
    try ctx.compile();
    try ctx.dump(std.io.getStdErr().writer());
    if (try ctx.printDiagnostics(src, std.io.getStdErr().writer()))
        return;
}
