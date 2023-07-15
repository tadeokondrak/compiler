const std = @import("std");
const sema = @import("sema");
const parse = @import("parse");
const syntax = @import("syntax");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{ .stack_trace_frames = 32 }) = .{};
    defer _ = gpa.deinit();

    const src =
        \\const num u32 = 1;
        \\const ptr *u64 = null;
        \\struct Struct {
        \\    field1 u32 = 1;
        \\    field2 *u32;
        \\}
        \\struct Node {
        \\    next *Node;
        \\}
        \\struct Other {
        \\    field1 Struct;
        \\}
        \\fn infinite_loop() (ret u32) {
        \\    loop {}
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
        \\fn add_generic<T>(a T, b T) (ret T) { return a + b; }
    ;

    var arena = std.heap.ArenaAllocator.init(gpa.allocator());
    defer arena.deinit();

    var parsed = try parse.parseFile(gpa.allocator(), src);
    defer parsed.root.deinit(gpa.allocator());

    var sctx: syntax.Context = .{
        .arena = arena.allocator(),
        .root = parsed.root,
    };

    var ctx: sema.Context = .{
        .gpa = gpa.allocator(),
        .ast = .{ .tree = try sctx.createTree(@enumFromInt(0)) },
    };
    defer ctx.deinit();

    for (
        parsed.root.errors.items(.message),
        parsed.root.errors.items(.span),
    ) |message, span| {
        try ctx.diagnostics.append(gpa.allocator(), .{
            .message = try gpa.allocator().dupe(u8, message),
            .span = span,
        });
    }

    // std.debug.print("syntax: {}\n", .{ctx.root});

    try ctx.compile();
    try ctx.dump(std.io.getStdErr().writer());
    if (try ctx.printDiagnostics(src, std.io.getStdErr().writer()))
        return;
}
