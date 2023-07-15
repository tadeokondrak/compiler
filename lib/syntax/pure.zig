//! Lossless homogenous syntax tree.
//!
//! See https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html for some context.

const std = @import("std");

pub const Builder = @import("pure/Builder.zig");

comptime {
    _ = Builder;
}

pub const Pos = struct {
    offset: u32,
};

pub const Span = struct {
    start: Pos,
    end: Pos,
};

pub const Node = struct {
    pub const Index = struct {
        bits: u32,

        const TREE_FLAG: u32 = 1 << 31;

        pub fn isTree(node: Node.Index) bool {
            return (node.bits & TREE_FLAG) != 0;
        }

        pub fn asTree(node: Node.Index) ?Tree.Index {
            if (!isTree(node)) return null;
            return @enumFromInt(node.bits & ~TREE_FLAG);
        }

        pub fn fromTree(tree: Tree.Index) Node.Index {
            return Node.Index{ .bits = @intFromEnum(tree) | TREE_FLAG };
        }

        pub fn fromTreeIndex(id: u32) Node.Index {
            return Node.Index{ .bits = id | TREE_FLAG };
        }

        pub fn isToken(node: Node.Index) bool {
            return (node.bits & TREE_FLAG) == 0;
        }

        pub fn asToken(node: Node.Index) ?Token.Index {
            if (!isToken(node)) return null;
            return @enumFromInt(node.bits);
        }

        pub fn fromToken(token: Token.Index) Node.Index {
            return Node.Index{ .bits = @intFromEnum(token) };
        }

        pub fn fromTokenIndex(id: u32) Node.Index {
            return Node.Index{ .bits = id };
        }
    };

    pub const Tag = struct {
        bits: u16,

        const TREE_FLAG: u16 = 1 << 15;

        pub fn isTreeTag(tag: Node.Tag) bool {
            return tag.bits & TREE_FLAG != 0;
        }

        pub fn asTreeTag(tag: Node.Tag) ?Tree.Tag {
            if (!isTreeTag(tag)) return null;
            return @enumFromInt(tag.bits & ~TREE_FLAG);
        }

        pub fn fromTreeTag(tag: Tree.Tag) Node.Tag {
            return Node.Tag{ .bits = @as(u16, @intFromEnum(tag)) | TREE_FLAG };
        }

        pub fn isTokenTag(tag: Node.Tag) bool {
            return tag.bits & TREE_FLAG == 0;
        }

        pub fn asTokenTag(tag: Node.Tag) ?Token.Tag {
            if (!isTokenTag(tag)) return null;
            return @enumFromInt(tag.bits);
        }

        pub fn fromTokenTag(tag: Token.Tag) Node.Tag {
            return Node.Tag{ .bits = @intFromEnum(tag) };
        }
    };
};

pub const Token = struct {
    tag: Token.Tag,
    pos: Pos,
    text_pos: u32,
    text_len: u32,
    trivia_start: u32,
    trivia_count: u32,

    pub const Index = enum(u32) { _ };

    pub const Tag = enum(u15) {
        invalid,
        eof,
        space,

        ident,
        number,
        string,

        plus,
        minus,
        star,
        slash,
        percent,

        lt,
        gt,
        eq,

        lt_eq,
        gt_eq,
        bang_eq,

        lt2,
        gt2,
        eq2,

        dot,
        bang,
        pipe,
        semi,
        caret,
        tilde,
        colon,
        comma,
        ampersand,

        l_paren,
        r_paren,
        l_bracket,
        r_bracket,
        l_brace,
        r_brace,

        kw_fn,
        kw_return,
        kw_struct,
        kw_const,
        kw_if,
        kw_else,
        kw_loop,
        kw_while,
        kw_break,
        kw_continue,
        kw_mut,
        kw_let,
    };
};

pub const Tree = struct {
    tag: Tree.Tag,
    children_pos: u32,
    children_len: u32,

    pub const Index = enum(u32) { _ };

    pub const Tag = enum(u15) {
        invalid,

        file,

        decl_fn,
        decl_const,
        decl_struct,

        expr_unary,
        expr_binary,
        expr_ident,
        expr_literal,
        expr_paren,
        expr_call,
        expr_index,

        stmt_block,
        stmt_expr,
        stmt_return,
        stmt_if,
        stmt_loop,
        stmt_while,
        stmt_break,
        stmt_continue,
        stmt_let,

        type_expr_unary,
        type_expr_ident,

        fn_params,
        fn_param,
        fn_returns,
        fn_return,
        call_args,
        call_arg,

        struct_field,

        generics,
        generic,
    };
};

pub const Child = struct {
    node: Node.Index,
    tag: Node.Tag,
};

pub const Trivia = struct {
    tag: Tag,
    count: u8,

    const Tag = enum(u8) {
        tab,
        space,
        newline,
        carriage_return,
    };
};

pub const Error = struct {
    message: []const u8,
    span: Span,
};

pub const Root = struct {
    errors: std.MultiArrayList(Error) = .{},
    tokens: std.MultiArrayList(Token) = .{},
    text: std.ArrayListUnmanaged(u8) = .{},
    trees: std.MultiArrayList(Tree) = .{},
    children: std.MultiArrayList(Child) = .{},
    trivia: std.MultiArrayList(Trivia) = .{},

    pub fn deinit(root: *Root, allocator: std.mem.Allocator) void {
        root.errors.deinit(allocator);
        root.tokens.deinit(allocator);
        root.text.deinit(allocator);
        root.trees.deinit(allocator);
        root.children.deinit(allocator);
        root.trivia.deinit(allocator);
    }

    // Token accessors

    pub fn tokenData(root: Root, id: Token.Index) Token {
        return root.tokens.get(@intFromEnum(id));
    }

    pub fn tokenTag(root: Root, id: Token.Index) Token.Tag {
        return root.tokenData(id).tag;
    }

    pub fn tokenPos(root: Root, id: Token.Index) Pos {
        return root.tokenData(id).pos;
    }

    pub fn tokenSpan(root: Root, id: Token.Index) Span {
        const data = root.tokenData(id);
        return .{ .start = data.pos, .end = .{ .offset = data.pos.offset + data.text_len } };
    }

    pub fn tokenText(root: Root, id: Token.Index) []const u8 {
        const data = root.tokenData(id);
        return root.text.items[data.text_pos .. data.text_pos + data.text_len];
    }

    // Tree accessors

    pub fn treeData(root: Root, id: Tree.Index) Tree {
        return root.trees.get(@intFromEnum(id));
    }

    pub fn treeTag(root: Root, id: Tree.Index) Tree.Tag {
        return root.treeData(id).tag;
    }

    pub fn treeStart(root: Root, id: Tree.Index) Pos {
        const children = root.treeChildren(id);
        const first_child = children[0];
        if (first_child.asTree()) |tree|
            return root.treeStart(tree);
        if (first_child.asToken()) |token|
            return root.tokenPos(token);
        unreachable;
    }

    pub fn treeEnd(root: Root, id: Tree.Index) Pos {
        const children = root.treeChildren(id);
        const last_child = children[children.len - 1];
        if (last_child.asTree()) |tree|
            return root.treeEnd(tree);
        if (last_child.asToken()) |token| {
            const data = root.tokenData(token);
            return Pos{ .offset = data.pos.offset + data.text_len };
        }
        unreachable;
    }

    pub fn treeSpan(root: Root, id: Tree.Index) Span {
        return Span{ .start = root.treeStart(id), .end = root.treeEnd(id) };
    }

    pub fn treeChildren(root: Root, id: Tree.Index) []const Node.Index {
        const data = root.treeData(id);
        return root.children.items(.node)[data.children_pos .. data.children_pos + data.children_len];
    }

    pub fn treeChildrenTags(root: Root, id: Tree.Index) []const Node.Tag {
        const data = root.treeData(id);
        return root.children.items(.tag)[data.children_pos .. data.children_pos + data.children_len];
    }

    // Formatting

    pub fn format(root: Root, comptime fmt: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        if (fmt.len != 0) @compileError("format string should be empty");
        if (root.trees.len > 0)
            try root.formatTree(@enumFromInt(0), 0, writer);
    }

    pub fn formatTree(root: Root, id: Tree.Index, indent: usize, writer: anytype) !void {
        const data = root.treeData(id);
        try writer.writeByteNTimes(' ', indent);
        try writer.print("{s}(\n", .{@tagName(data.tag)});
        for (root.treeChildren(id)) |node| {
            if (node.asToken()) |token|
                try root.formatToken(token, indent + 2, writer)
            else if (node.asTree()) |tree|
                try root.formatTree(tree, indent + 2, writer)
            else
                unreachable;
            try writer.writeByte('\n');
        }
        try writer.writeByteNTimes(' ', indent);
        try writer.writeAll(")");
    }

    pub fn formatToken(root: Root, id: Token.Index, indent: usize, writer: anytype) !void {
        const data = root.tokenData(id);
        const text = root.text.items[data.text_pos .. data.text_pos + data.text_len];
        if (data.trivia_count != 0) {
            for (data.trivia_start..data.trivia_start + data.trivia_count) |i| {
                const trivia = root.trivia.get(i);
                try writer.writeByteNTimes(' ', indent);
                try writer.print("// {s}({})\n", .{ @tagName(trivia.tag), trivia.count });
            }
        }
        try writer.writeByteNTimes(' ', indent);
        try writer.print("{s}(\"{}\")", .{ @tagName(data.tag), std.zig.fmtEscapes(text) });
    }

    pub fn format2(root: Root, writer: anytype) !void {
        try root.formatTree2(@enumFromInt(0), writer);
    }

    pub fn formatTree2(root: Root, id: Tree.Index, writer: anytype) !void {
        for (root.treeChildren(id)) |node| {
            if (node.asToken()) |token|
                try root.formatToken2(token, writer)
            else if (node.asTree()) |tree|
                try root.formatTree2(tree, writer)
            else
                unreachable;
        }
    }

    pub fn formatToken2(root: Root, id: Token.Index, writer: anytype) !void {
        const data = root.tokenData(id);
        const text = root.text.items[data.text_pos .. data.text_pos + data.text_len];
        if (data.trivia_count != 0) {
            for (data.trivia_start..data.trivia_start + data.trivia_count) |i| {
                const trivia = root.trivia.get(i);
                const byte: u8 = switch (trivia.tag) {
                    .tab => '\t',
                    .space => ' ',
                    .newline => '\n',
                    .carriage_return => '\r',
                };
                try writer.writeByteNTimes(byte, trivia.count);
            }
        }
        try writer.writeAll(text);
    }
};

test Root {
    var root: Root = .{};
    defer root.deinit(std.testing.allocator);

    try root.text.append(std.testing.allocator, '1');

    const token_id: Token.Index = @enumFromInt(0);
    const token_data = Token{
        .tag = .number,
        .pos = .{ .offset = 0 },
        .text_pos = 0,
        .text_len = 1,
        .trivia_start = 0,
        .trivia_count = 0,
    };
    try root.tokens.append(std.testing.allocator, token_data);
    try std.testing.expectEqual(token_data, root.tokenData(token_id));
    try std.testing.expectEqual(Token.Tag.number, root.tokenTag(token_id));
    try std.testing.expectEqualSlices(u8, "1", root.tokenText(token_id));

    const tree_id: Tree.Index = @enumFromInt(@as(u32, @intCast(root.trees.len)));
    const tree_data = Tree{ .tag = .expr_literal, .children_pos = 0, .children_len = 1 };
    try root.trees.append(std.testing.allocator, tree_data);
    try root.children.append(std.testing.allocator, .{
        .node = Node.Index.fromToken(token_id),
        .tag = Node.Tag.fromTokenTag(token_data.tag),
    });
    try std.testing.expectEqual(tree_data, root.treeData(tree_id));
    try std.testing.expectEqual(Tree.Tag.expr_literal, root.treeTag(tree_id));
    try std.testing.expectEqualSlices(Node.Index, &.{Node.Index.fromToken(token_id)}, root.treeChildren(tree_id));
    try std.testing.expectEqual(@as(?Tree.Index, null), root.treeChildren(tree_id)[0].asTree());
    try std.testing.expectEqual(@as(?Token.Index, token_id), root.treeChildren(tree_id)[0].asToken());

    const text = try std.fmt.allocPrint(std.testing.allocator, "{}", .{root});
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualSlices(u8,
        \\expr_literal(
        \\  number("1")
        \\)
    ++ "\n", text);
}
