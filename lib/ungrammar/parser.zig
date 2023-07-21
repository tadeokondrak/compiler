const std = @import("std");
const lexer = @import("lexer.zig");
const ungrammar = @import("ungrammar.zig");

pub const ParseResult = union(enum) {
    success: ungrammar.Grammar,
    failure: struct {
        message: []const u8,
        position: usize,
    },

    pub fn deinit(p: *ParseResult, allocator: std.mem.Allocator) void {
        switch (p.*) {
            .success => |*grammar| grammar.deinit(allocator),
            .failure => |failure| allocator.free(failure.message),
        }
    }
};

const Token = struct {
    tag: lexer.Token.Tag,
    pos: usize,
};

pub fn parse(allocator: std.mem.Allocator, src: []const u8) error{OutOfMemory}!ParseResult {
    var parser: Parser = .{ .allocator = allocator, .src = src, .input = undefined };
    errdefer parser.deinit();

    var tokens: std.MultiArrayList(Token) = .{};
    defer tokens.deinit(allocator);

    var pos: usize = 0;
    while (lexer.tokenize(src[pos..])) |token| : (pos += token.len) {
        const text = src[pos..][0..token.len];
        switch (token.tag) {
            .invalid => {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "invalid token '{s}'",
                    .{text},
                );

                parser.deinit();

                return .{
                    .failure = .{
                        .message = message,
                        .position = pos,
                    },
                };
            },
            .whitespace, .comment => {
                // skip
            },
            else => |tag| {
                try tokens.append(allocator, .{
                    .tag = tag,
                    .pos = pos,
                });
            },
        }
    }

    parser.input = tokens.slice();

    parser.parseGrammar() catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Syntax => {
            parser.deinit();

            return .{
                .failure = .{
                    .message = parser.@"error".message,
                    .position = parser.@"error".position,
                },
            };
        },
    };

    return .{ .success = try parser.toGrammar() };
}

const Parser = struct {
    allocator: std.mem.Allocator,

    @"error": struct {
        message: []const u8,
        position: usize,
    } = undefined,

    src: []const u8,
    input: std.MultiArrayList(Token).Slice,
    input_pos: usize = 0,

    text: std.ArrayListUnmanaged(u8) = .{},
    extra: std.ArrayListUnmanaged(u32) = .{},
    tokens: std.ArrayListUnmanaged(ungrammar.Token) = .{},
    nodes: std.MultiArrayList(ungrammar.Node) = .{},
    rules: std.MultiArrayList(ungrammar.Rule) = .{},
    node_lookup: std.AutoArrayHashMapUnmanaged(void, void) = .{},
    token_lookup: std.AutoArrayHashMapUnmanaged(void, void) = .{},

    fn deinit(parser: *Parser) void {
        parser.node_lookup.deinit(parser.allocator);
        parser.token_lookup.deinit(parser.allocator);
        parser.text.deinit(parser.allocator);
        parser.tokens.deinit(parser.allocator);
        parser.nodes.deinit(parser.allocator);
        parser.rules.deinit(parser.allocator);
    }

    fn toGrammar(parser: *Parser) error{OutOfMemory}!ungrammar.Grammar {
        parser.node_lookup.deinit(parser.allocator);
        parser.token_lookup.deinit(parser.allocator);

        const text = try parser.text.toOwnedSlice(parser.allocator);
        errdefer parser.allocator.free(text);

        const extra = try parser.extra.toOwnedSlice(parser.allocator);
        errdefer parser.allocator.free(extra);

        const tokens = try parser.tokens.toOwnedSlice(parser.allocator);
        errdefer parser.allocator.free(tokens);

        var nodes = parser.nodes.toOwnedSlice();
        errdefer nodes.deinit(parser.allocator);

        var rules = parser.rules.toOwnedSlice();
        errdefer rules.deinit(parser.allocator);

        return .{
            .text = text,
            .tokens = tokens,
            .extra = extra,
            .nodes = nodes,
            .rules = rules,
        };
    }

    fn advance(parser: *Parser) usize {
        parser.input_pos += 1;
        return parser.input.items(.pos)[parser.input_pos - 1];
    }

    fn nth(parser: Parser, n: usize) ?lexer.Token.Tag {
        if (parser.input_pos + n >= parser.input.len)
            return null;

        return parser.input.items(.tag)[parser.input_pos + n];
    }

    fn at(parser: Parser, tag: lexer.Token.Tag) bool {
        return parser.nth(0) == tag;
    }

    fn atAny(parser: Parser, tags: []const lexer.Token.Tag) bool {
        for (tags) |tag|
            if (parser.at(tag))
                return true;

        return false;
    }

    fn eat(parser: *Parser, tag: lexer.Token.Tag) ?usize {
        if (!parser.at(tag))
            return null;
        return parser.advance();
    }

    fn expect(parser: *Parser, tag: lexer.Token.Tag) error{ Syntax, OutOfMemory }!usize {
        if (!parser.at(tag)) {
            if (parser.nth(0)) |got| {
                parser.@"error".message = try std.fmt.allocPrint(parser.allocator, "expected '{s}', got '{s}'", .{ @tagName(tag), @tagName(got) });
                parser.@"error".position = parser.input.items(.pos)[parser.input_pos];
            } else {
                parser.@"error".message = try std.fmt.allocPrint(parser.allocator, "expected '{s}', reached end of file", .{@tagName(tag)});
                parser.@"error".position = parser.input.items(.pos)[parser.input_pos - 1];
            }

            return error.Syntax;
        }
        return parser.advance();
    }

    fn expectAny(parser: *Parser, comptime tags: []const lexer.Token.Tag) error{ Syntax, OutOfMemory }!Token {
        if (!parser.atAny(tags)) {
            // TODO: nicer error
            parser.@"error".message = try if (parser.nth(0)) |got|
                std.fmt.allocPrint(parser.allocator, "expected {any}, got {s}", .{ tags, @tagName(got) })
            else
                std.fmt.allocPrint(parser.allocator, "expected {any}, reached end of file", .{tags});
            parser.@"error".position = parser.input.items(.pos)[parser.input_pos];
            return error.Syntax;
        }
        return .{
            .tag = parser.nth(0).?,
            .pos = parser.advance(),
        };
    }

    fn parseGrammar(parser: *Parser) error{ Syntax, OutOfMemory }!void {
        while (parser.input_pos < parser.input.len)
            _ = try parser.parseNode();
    }

    fn parseNode(parser: *Parser) error{ Syntax, OutOfMemory }!ungrammar.Node.Index {
        const name_pos = try parser.expect(.name);
        const name = parser.getNameText(name_pos);
        _ = try parser.expect(.equal_sign);
        const rule = try parser.parseAltRule();
        const node = try parser.getNode(name);
        parser.nodes.items(.rule)[@intFromEnum(node)] = rule;
        return @enumFromInt(parser.nodes.len - 1);
    }

    fn parseAltRule(parser: *Parser) error{ Syntax, OutOfMemory }!ungrammar.Rule.Index {
        const lhs = try parser.parseSeqRule();
        while (parser.at(.vertical_bar)) {
            _ = parser.advance();
            const rhs = try parser.parseAltRule();
            const extra: u32 = @intCast(parser.extra.items.len);
            try parser.extra.appendSlice(parser.allocator, &.{
                @intFromEnum(lhs),
                @intFromEnum(rhs),
            });
            try parser.rules.append(parser.allocator, .{
                .tag = .alt,
                .data = .{ .extra = extra },
            });
            return @enumFromInt(parser.rules.len - 1);
        }
        return lhs;
    }

    fn parseSeqRule(parser: *Parser) error{ Syntax, OutOfMemory }!ungrammar.Rule.Index {
        const lhs = try parser.parseLabeledRule();
        while (true) {
            if (parser.nth(0) == null or
                parser.nth(0) == .name and parser.nth(1) == .equal_sign or
                parser.nth(0) == .right_parenthesis or
                parser.nth(0) == .vertical_bar)
            {
                return lhs;
            }
            const rhs = try parser.parseSeqRule();
            const extra: u32 = @intCast(parser.extra.items.len);
            try parser.extra.appendSlice(parser.allocator, &.{
                @intFromEnum(lhs),
                @intFromEnum(rhs),
            });
            try parser.rules.append(parser.allocator, .{
                .tag = .seq,
                .data = .{ .extra = extra },
            });
            return @enumFromInt(parser.rules.len - 1);
        }
    }

    fn parseLabeledRule(parser: *Parser) error{ Syntax, OutOfMemory }!ungrammar.Rule.Index {
        if (parser.nth(0) == .name and parser.nth(1) == .colon) {
            const label_pos = parser.advance();
            const label = parser.getNameText(label_pos);
            _ = parser.advance();
            const rule = try parser.parseUnlabeledRule();
            const label_text_pos = parser.text.items.len;
            try parser.text.ensureUnusedCapacity(parser.allocator, label.len + 1);
            parser.text.appendSliceAssumeCapacity(label);
            parser.text.appendAssumeCapacity(0);
            const extra: u32 = @intCast(parser.extra.items.len);
            try parser.extra.appendSlice(parser.allocator, &.{
                @as(u32, @intCast(label_text_pos)),
                @intFromEnum(rule),
            });
            try parser.rules.append(parser.allocator, .{
                .tag = .label,
                .data = .{ .extra = extra },
            });
            return @enumFromInt(parser.rules.len - 1);
        }
        return parser.parseUnlabeledRule();
    }

    fn parseUnlabeledRule(parser: *Parser) error{ Syntax, OutOfMemory }!ungrammar.Rule.Index {
        const input = try parser.expectAny(&.{ .left_parenthesis, .name, .token_name });
        const rule: ungrammar.Rule.Index = switch (input.tag) {
            .left_parenthesis => blk: {
                const rule = try parser.parseAltRule();
                _ = try parser.expect(.right_parenthesis);
                break :blk rule;
            },
            .name => blk: {
                const name = parser.getNameText(input.pos);
                const node = try parser.getNode(name);
                try parser.rules.append(parser.allocator, .{ .tag = .node, .data = .{ .node = node } });
                break :blk @enumFromInt(parser.rules.len - 1);
            },
            .token_name => blk: {
                const name = parser.getTokenNameText(input.pos);
                const token = try parser.getToken(name);
                try parser.rules.append(parser.allocator, .{ .tag = .token, .data = .{ .token = token } });
                break :blk @enumFromInt(parser.rules.len - 1);
            },
            else => unreachable,
        };
        if (parser.eat(.question_mark)) |_| {
            try parser.rules.append(parser.allocator, .{ .tag = .opt, .data = .{ .rule = rule } });
            return @enumFromInt(parser.rules.len - 1);
        }
        if (parser.eat(.asterisk)) |_| {
            try parser.rules.append(parser.allocator, .{ .tag = .rep, .data = .{ .rule = rule } });
            return @enumFromInt(parser.rules.len - 1);
        }
        return rule;
    }

    fn getNameText(parser: Parser, pos: usize) []const u8 {
        for (parser.src[pos..], pos..) |c, i| {
            switch (c) {
                'a'...'z', 'A'...'Z', '_' => {},
                else => return parser.src[pos..i],
            }
        }
        return parser.src[pos..];
    }

    fn getTokenNameText(parser: Parser, pos: usize) []const u8 {
        var escaped = false;
        for (parser.src[pos + 1 ..], pos + 1..) |c, i| {
            switch (c) {
                '\\' => escaped = !escaped,
                '\'' => {
                    if (escaped) {
                        escaped = false;
                        continue;
                    }
                    return parser.src[pos + 1 .. i];
                },
                else => std.debug.assert(!escaped),
            }
        }
        unreachable;
    }

    fn getNode(parser: *Parser, name: []const u8) error{OutOfMemory}!ungrammar.Node.Index {
        const result = try parser.node_lookup.getOrPutAdapted(parser.allocator, name, struct {
            name_pos: []const u32,
            text: []const u8,

            pub fn hash(_: @This(), val: []const u8) u32 {
                return @truncate(std.hash.Wyhash.hash(0, val));
            }

            pub fn eql(this: @This(), lhs: []const u8, _: void, rhs_index: usize) bool {
                const rhs_pos = this.name_pos[rhs_index];
                var rhs_end = rhs_pos;
                while (this.text[rhs_end] != 0)
                    rhs_end += 1;
                return std.mem.eql(u8, lhs, this.text[rhs_pos..rhs_end]);
            }
        }{ .name_pos = parser.nodes.items(.name_pos), .text = parser.text.items });

        if (!result.found_existing) {
            std.debug.assert(result.index == try parser.nodes.addOne(parser.allocator));

            const name_pos = parser.text.items.len;

            try parser.text.ensureUnusedCapacity(parser.allocator, name.len + 1);
            parser.text.appendSliceAssumeCapacity(name);
            parser.text.appendAssumeCapacity(0);

            parser.nodes.items(.name_pos)[result.index] = @intCast(name_pos);
            parser.nodes.items(.rule)[result.index] = @enumFromInt(std.math.maxInt(u32));
        }

        return @enumFromInt(result.index);
    }

    fn getToken(parser: *Parser, name: []const u8) error{OutOfMemory}!ungrammar.Token.Index {
        const result = try parser.token_lookup.getOrPutAdapted(parser.allocator, name, struct {
            tokens: []const ungrammar.Token,
            text: []const u8,

            pub fn hash(_: @This(), val: []const u8) u32 {
                return @truncate(std.hash.Wyhash.hash(0, val));
            }

            pub fn eql(this: @This(), lhs: []const u8, _: void, rhs_index: usize) bool {
                const rhs_pos = this.tokens[rhs_index].name_pos;
                var rhs_end = rhs_pos;
                while (this.text[rhs_end] != 0)
                    rhs_end += 1;
                return std.mem.eql(u8, lhs, this.text[rhs_pos..rhs_end]);
            }
        }{ .tokens = parser.tokens.items, .text = parser.text.items });

        if (!result.found_existing) {
            std.debug.assert(result.index == parser.tokens.items.len);

            const name_pos = parser.text.items.len;

            try parser.text.ensureUnusedCapacity(parser.allocator, name.len + 1);
            for (name, 0..) |c, i| {
                if (c == '\\' and (i == 0 or name[i - 1] != '\\'))
                    continue;
                parser.text.appendAssumeCapacity(c);
            }
            parser.text.appendAssumeCapacity(0);

            try parser.tokens.append(parser.allocator, .{ .name_pos = @intCast(name_pos) });
        }

        return @enumFromInt(result.index);
    }
};

test parse {
    {
        var parsed = try parse(std.testing.allocator,
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
        defer parsed.deinit(std.testing.allocator);

        try std.testing.expect(parsed == .success);

        const grammar = parsed.success;

        var names = std.ArrayList([]const u8).init(std.testing.allocator);
        defer names.deinit();

        for (0..grammar.nodes.len) |node_index| {
            const node: ungrammar.Node.Index = @enumFromInt(node_index);
            try names.append(grammar.nodeName(node));
        }

        try std.testing.expectEqualDeep(
            @as([]const []const u8, &.{ "Node", "Rule", "Grammar" }),
            names.items,
        );
    }

    {
        var parsed = try parse(std.testing.allocator,
            \\Quote = '\''
            \\Backslash = '\\'
        );
        defer parsed.deinit(std.testing.allocator);

        try std.testing.expect(parsed == .success);
        try std.testing.expectEqualStrings(
            "'\x00Quote\x00\\\x00Backslash\x00",
            parsed.success.text,
        );
    }

    {
        var parsed = try parse(std.testing.allocator,
            \\Node = 'token'
            \\Node = 'token'
        );
        defer parsed.deinit(std.testing.allocator);

        // TODO
        // try std.testing.expect(parsed == .failure);
    }

    {
        var parsed = try parse(std.testing.allocator,
            \\Node = OtherNode
        );
        defer parsed.deinit(std.testing.allocator);

        // TODO
        // try std.testing.expect(parsed == .failure);
    }
}
