const sema = @import("sema");
const syntax = @import("syntax");
const parse = @import("parse");
const std = @import("std");

fn check(src: []const u8, diagnostics: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parsed = try parse.parseFile(std.testing.allocator, src);
    defer parsed.root.deinit(std.testing.allocator);

    var sctx: syntax.Context = .{
        .arena = arena.allocator(),
        .root = parsed.root,
    };

    var ctx: sema.Sema = .{
        .gpa = std.testing.allocator,
        .ast = .{ .tree = try sctx.createTree(@enumFromInt(0)) },
    };
    defer ctx.deinit();

    for (
        parsed.root.errors.items(.message),
        parsed.root.errors.items(.span),
    ) |message, span| {
        try ctx.diagnostics.append(std.testing.allocator, .{
            .message = try std.testing.allocator.dupe(u8, message),
            .span = span,
        });
    }

    var it = ctx.ast.declNodes();
    while (try it.next()) |decl_syntax|
        try ctx.analyzeDecl(decl_syntax);

    var errors = std.ArrayList(u8).init(std.testing.allocator);
    defer errors.deinit();

    for (ctx.diagnostics.items(.message), 0..) |message, i| {
        if (i > 0) try errors.append('\n');
        try errors.appendSlice(message);
    }

    try std.testing.expectEqualStrings(diagnostics, errors.items);
}

test "basic" {
    try check(
        \\const x u32 = null;
    ,
        \\expected u32, got untyped null
    );
}
