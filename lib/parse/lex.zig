const std = @import("std");
const syntax = @import("syntax");

pub const Token = struct {
    tag: syntax.pure.Token.Tag,
    len: usize,
};

const kw_map = std.ComptimeStringMap(syntax.pure.Token.Tag, .{
    .{ "fn", .kw_fn },
    .{ "return", .kw_return },
    .{ "struct", .kw_struct },
    .{ "const", .kw_const },
    .{ "if", .kw_if },
    .{ "loop", .kw_loop },
    .{ "while", .kw_while },
});

pub const Lexer = struct {
    pos: usize = 0,
    text: []const u8,

    pub fn nth(lexer: *Lexer, n: usize) u8 {
        if (lexer.pos + n >= lexer.text.len) return 0;
        return lexer.text[lexer.pos + n];
    }

    pub fn next(lexer: *Lexer) ?Token {
        const State = union(enum) {
            init,
            ident: struct { start_pos: usize },
            number: struct { start_pos: usize },
            space: struct { start_pos: usize },
        };

        var state: State = .init;
        if (lexer.pos >= lexer.text.len)
            return null;
        while (true) {
            switch (state) {
                .init => switch (lexer.nth(0)) {
                    // zig fmt: off
                    '(' => { lexer.pos += 1; return Token{ .tag = .l_paren, .len = 1 }; },
                    ')' => { lexer.pos += 1; return Token{ .tag = .r_paren, .len = 1 }; },
                    '[' => { lexer.pos += 1; return Token{ .tag = .l_bracket, .len = 1 }; },
                    ']' => { lexer.pos += 1; return Token{ .tag = .r_bracket, .len = 1 }; },
                    '{' => { lexer.pos += 1; return Token{ .tag = .l_brace, .len = 1 }; },
                    '}' => { lexer.pos += 1; return Token{ .tag = .r_brace, .len = 1 }; },
                    '+' => { lexer.pos += 1; return Token{ .tag = .plus, .len = 1 }; },
                    '-' => { lexer.pos += 1; return Token{ .tag = .minus, .len = 1 }; },
                    '*' => { lexer.pos += 1; return Token{ .tag = .star, .len = 1 }; },
                    '/' => { lexer.pos += 1; return Token{ .tag = .slash, .len = 1 }; },
                    '%' => { lexer.pos += 1; return Token{ .tag = .percent, .len = 1 }; },
                    '&' => { lexer.pos += 1; return Token{ .tag = .ampersand, .len = 1 }; },
                    '^' => { lexer.pos += 1; return Token{ .tag = .caret, .len = 1 }; },
                    '|' => { lexer.pos += 1; return Token{ .tag = .pipe, .len = 1 }; },
                    ';' => { lexer.pos += 1; return Token{ .tag = .semi, .len = 1 }; },
                    ':' => { lexer.pos += 1; return Token{ .tag = .colon, .len = 1 }; },
                    ',' => { lexer.pos += 1; return Token{ .tag = .comma, .len = 1 }; },
                    '=' => switch (lexer.nth(1)) {
                        '=' => { lexer.pos += 2; return Token{ .tag = .eq2, .len = 2 }; },
                        else => { lexer.pos += 1; return Token{ .tag = .eq, .len = 1 }; },
                    },
                    '<' => switch (lexer.nth(1)) {
                        '<' => { lexer.pos += 2; return Token{ .tag = .lt2, .len = 2 }; },
                        '=' => { lexer.pos += 2; return Token{ .tag = .lt_eq, .len = 2 }; },
                        else => { lexer.pos += 1; return Token{ .tag = .lt, .len = 1 }; },
                    },
                    '>' => switch (lexer.nth(1)) {
                        '>' => { lexer.pos += 2; return Token{ .tag = .gt2, .len = 2 }; },
                        '=' => { lexer.pos += 2; return Token{ .tag = .gt_eq, .len = 2 }; },
                        else => { lexer.pos += 1; return Token{ .tag = .gt, .len = 1 }; },
                    },
                    // zig fmt: on
                    'a'...'z', 'A'...'Z', '_' => {
                        state = .{ .ident = .{ .start_pos = lexer.pos } };
                        lexer.pos += 1;
                    },
                    '0'...'9' => {
                        state = .{ .number = .{ .start_pos = lexer.pos } };
                        lexer.pos += 1;
                    },
                    ' ', '\r', '\n', '\t' => {
                        state = .{ .space = .{ .start_pos = lexer.pos } };
                        lexer.pos += 1;
                    },
                    else => {
                        lexer.pos += 1;
                        return Token{ .tag = .invalid, .len = 1 };
                    },
                },
                .ident => |ident_state| switch (lexer.nth(0)) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_' => lexer.pos += 1,
                    else => {
                        const text = lexer.text[ident_state.start_pos..lexer.pos];
                        const tag = kw_map.get(text) orelse .ident;
                        return Token{ .tag = tag, .len = lexer.pos - ident_state.start_pos };
                    },
                },
                .number => |number_state| switch (lexer.nth(0)) {
                    '0'...'9' => lexer.pos += 1,
                    else => return Token{ .tag = .number, .len = lexer.pos - number_state.start_pos },
                },
                .space => |space_state| switch (lexer.nth(0)) {
                    ' ', '\r', '\n', '\t' => lexer.pos += 1,
                    else => return Token{ .tag = .space, .len = lexer.pos - space_state.start_pos },
                },
            }
        }
    }
};

test Lexer {
    const text = "1 + 2 * 3";
    var lexer = Lexer{ .text = text };
    for ([_]Token{
        .{ .tag = .number, .len = 1 },
        .{ .tag = .space, .len = 1 },
        .{ .tag = .plus, .len = 1 },
        .{ .tag = .space, .len = 1 },
        .{ .tag = .number, .len = 1 },
        .{ .tag = .space, .len = 1 },
        .{ .tag = .star, .len = 1 },
        .{ .tag = .space, .len = 1 },
        .{ .tag = .number, .len = 1 },
    }) |token| {
        try std.testing.expectEqual(@as(?Token, token), lexer.next());
    }
    try std.testing.expectEqual(@as(?Token, null), lexer.next());
}
