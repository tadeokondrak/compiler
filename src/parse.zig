const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("parse/lex.zig");

const Parser = @import("parse/Parser.zig");
const grammar = @import("parse/grammar.zig");

comptime {
    _ = Parser;
    _ = grammar;
    _ = lex;
}

pub const Parse = struct {
    root: syntax.pure.Root,
    ast: syntax.ast.File,
};

pub fn parseFile(allocator: std.mem.Allocator, src: []const u8) error{OutOfMemory}!Parse {
    var tokens = std.ArrayListUnmanaged(syntax.pure.Token.Tag){};
    defer tokens.deinit(allocator);

    var all_tokens = std.MultiArrayList(lex.Token){};
    defer all_tokens.deinit(allocator);

    var l = lex.Lexer{ .text = src };
    var pos: usize = 0;
    while (l.next()) |token| {
        if (token.tag != .space)
            try tokens.append(allocator, token.tag);
        try all_tokens.append(allocator, token);
        pos += token.len;
    }

    var parser = Parser{
        .tokens = tokens.items,
        .builder = syntax.pure.Builder{
            .allocator = allocator,
        },
    };
    defer parser.deinit();

    grammar.parseFile(&parser);

    return Parse{
        .root = try parser.builder.build(
            allocator,
            src,
            all_tokens.items(.tag),
            all_tokens.items(.len),
        ),
        .ast = syntax.ast.File{
            .tree = @intToEnum(syntax.pure.Tree.Index, 0),
        },
    };
}
