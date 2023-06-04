const std = @import("std");
const syntax = @import("syntax.zig");
const lexer = @import("lex.zig");
const ast = @import("ast.zig");

const Parser = @import("parse/Parser.zig");

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
