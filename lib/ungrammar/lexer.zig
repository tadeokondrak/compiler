const std = @import("std");

pub const Token = struct {
    tag: Tag,
    len: usize,

    pub const Tag = enum {
        invalid,
        comment,
        whitespace,
        equal_sign,
        vertical_bar,
        question_mark,
        asterisk,
        colon,
        left_parenthesis,
        right_parenthesis,
        name,
        token_name,
    };
};

fn indexOfFuncPos(comptime T: type, slice: []const T, start_index: usize, func: fn (T) bool) ?usize {
    var i: usize = start_index;
    while (i < slice.len) : (i += 1)
        if (func(slice[i])) return i;
    return null;
}

fn isTokenStart(c: u8) bool {
    return switch (c) {
        ' ',
        '\t',
        '\n',
        '=',
        '|',
        '?',
        '*',
        ':',
        '(',
        ')',
        '\'',
        '_',
        '/',
        '"',
        'a'...'z',
        'A'...'Z',
        => true,
        else => false,
    };
}

pub fn tokenize(text: []const u8) ?Token {
    if (text.len == 0) return null;
    return switch (text[0]) {
        ' ',
        '\t',
        '\n',
        => {
            for (text[1..], 1..) |c, i| switch (c) {
                ' ', '\t', '\n' => continue,
                else => return .{ .tag = .whitespace, .len = i },
            };
            return .{ .tag = .whitespace, .len = text.len };
        },
        '=' => .{ .tag = .equal_sign, .len = 1 },
        '|' => .{ .tag = .vertical_bar, .len = 1 },
        '?' => .{ .tag = .question_mark, .len = 1 },
        '*' => .{ .tag = .asterisk, .len = 1 },
        ':' => .{ .tag = .colon, .len = 1 },
        '(' => .{ .tag = .left_parenthesis, .len = 1 },
        ')' => .{ .tag = .right_parenthesis, .len = 1 },
        '_',
        'a'...'z',
        'A'...'Z',
        => {
            for (text, 0..) |c, i| switch (c) {
                '_',
                'a'...'z',
                'A'...'Z',
                => {},
                else => return .{ .tag = .name, .len = i },
            };
            return .{ .tag = .name, .len = text.len };
        },
        '\'' => {
            var escaped = false;
            var invalid_escape = false;
            for (text[1..], 1..) |c, i| switch (c) {
                '\\' => escaped = !escaped,
                '\'' => {
                    if (escaped) {
                        escaped = false;
                        continue;
                    }
                    return .{
                        .tag = if (invalid_escape) .invalid else .token_name,
                        .len = i + 1,
                    };
                },
                else => {
                    invalid_escape = invalid_escape or escaped;
                    escaped = false;
                },
            };
            return .{ .tag = .invalid, .len = text.len };
        },
        '/' => {
            if (text.len <= 1 or text[1] != '/') {
                return .{
                    .tag = .invalid,
                    .len = indexOfFuncPos(u8, text, 1, isTokenStart) orelse text.len,
                };
            }
            return .{
                .tag = .comment,
                .len = (std.mem.indexOfScalar(u8, text, '\n') orelse text.len - 1) + 1,
            };
        },
        else => .{
            .tag = .invalid,
            .len = indexOfFuncPos(u8, text, 0, isTokenStart) orelse text.len,
        },
    };
}

fn expectTokens(text: []const u8, expected_tokens: []const Token) !void {
    var tokens: std.ArrayListUnmanaged(Token) = .{};
    defer tokens.deinit(std.testing.allocator);

    var text_remaining = text;
    while (true) {
        const token = tokenize(text_remaining) orelse break;
        try tokens.append(std.testing.allocator, token);
        text_remaining = text_remaining[token.len..];
    }

    return std.testing.expectEqualSlices(Token, expected_tokens, tokens.items);
}

fn expectNoInvalidTokens(text: []const u8) !void {
    var text_remaining = text;
    while (true) {
        const token = tokenize(text_remaining) orelse break;
        text_remaining = text_remaining[token.len..];
        try std.testing.expect(token.len != 0);
        try std.testing.expect(token.tag != .invalid);
    }
}

test tokenize {
    try expectTokens("Test", &.{
        .{ .tag = .name, .len = 4 },
    });

    try expectTokens("// Test\n", &.{
        .{ .tag = .comment, .len = 8 },
    });
    try expectTokens("// Test", &.{
        .{ .tag = .comment, .len = 7 },
    });

    try expectTokens("/$", &.{
        .{ .tag = .invalid, .len = 2 },
    });

    try expectTokens(
        \\'\x' x
    , &.{
        .{ .tag = .invalid, .len = 4 },
        .{ .tag = .whitespace, .len = 1 },
        .{ .tag = .name, .len = 1 },
    });

    try expectTokens(
        \\'x' '\'' '\\'
    , &.{
        .{ .tag = .token_name, .len = 3 },
        .{ .tag = .whitespace, .len = 1 },
        .{ .tag = .token_name, .len = 4 },
        .{ .tag = .whitespace, .len = 1 },
        .{ .tag = .token_name, .len = 4 },
    });

    try expectTokens("Test \t\nTest", &.{
        .{ .tag = .name, .len = 4 },
        .{ .tag = .whitespace, .len = 3 },
        .{ .tag = .name, .len = 4 },
    });

    try expectNoInvalidTokens(
        \\Grammar =
        \\  Node*
        \\
        \\Node =
        \\  name:'ident' '=' Rule
        \\
        \\Rule =
        \\  'ident'                // Alphabetic identifier
        \\| 'token_ident'          // Single quoted string
        \\| Rule*                  // Concatenation
        \\| Rule ('|' Rule)*       // Alternation
        \\| Rule '?'               // Zero or one repetition
        \\| Rule '*'               // Kleene star
        \\| '(' Rule ')'           // Grouping
        \\| label:'ident' ':' Rule // Labeled rule
    );
}
