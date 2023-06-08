//! Lossless homogenous syntax tree.
//!
//! See https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html for some context.

const std = @import("std");

pub const Builder = @import("syntax/Builder.zig");

comptime {
    _ = Builder;
}

pub const Node = struct {
    pub const Index = struct {
        bits: u32,

        const TREE_FLAG: u32 = 1 << 31;

        pub fn isTree(node: Node.Index) bool {
            return (node.bits & TREE_FLAG) != 0;
        }

        pub fn asTree(node: Node.Index) ?Tree.Index {
            if (!isTree(node)) return null;
            return Tree.Index{ .index = node.bits & ~TREE_FLAG };
        }

        pub fn fromTree(tree: Tree.Index) Node.Index {
            return Node.Index{ .bits = tree.index | TREE_FLAG };
        }

        pub fn fromTreeIndex(id: u32) Node.Index {
            return Node.Index{ .bits = id | TREE_FLAG };
        }

        pub fn isToken(node: Node.Index) bool {
            return (node.bits & TREE_FLAG) == 0;
        }

        pub fn asToken(node: Node.Index) ?Token.Index {
            if (!isToken(node)) return null;
            return Token.Index{ .index = node.bits };
        }

        pub fn fromToken(token: Token.Index) Node.Index {
            return Node.Index{ .bits = token.index };
        }

        pub fn fromTokenIndex(id: u32) Node.Index {
            return Node.Index{ .bits = id };
        }
    };

    pub const Tag = struct {
        bits: u16,

        const TREE_FLAG: u16 = 1 << 15;

        pub fn isTreeTag(tag: Node.Tag) bool {
            //return (@enumToInt(tag) & TREE_FLAG) != 0;
            return tag.bits & TREE_FLAG != 0;
        }

        pub fn asTreeTag(tag: Node.Tag) ?Tree.Tag {
            if (!isTreeTag(tag)) return null;
            return @intToEnum(Tree.Tag, tag.bits & ~TREE_FLAG);
        }

        pub fn fromTreeTag(tag: Tree.Tag) Node.Tag {
            return Node.Tag{ .bits = @as(u16, @enumToInt(tag)) | TREE_FLAG };
        }

        pub fn isTokenTag(tag: Node.Tag) bool {
            return tag.bits & TREE_FLAG == 0;
        }

        pub fn asTokenTag(tag: Node.Tag) ?Token.Tag {
            if (!isTokenTag(tag)) return null;
            return @intToEnum(Token.Tag, tag.bits);
        }

        pub fn fromTokenTag(tag: Token.Tag) Node.Tag {
            return Node.Tag{ .bits = @enumToInt(tag) };
        }
    };
};

pub const Token = struct {
    tag: Token.Tag,
    text_pos: u32,
    text_len: u32,

    pub const Index = struct { index: u32 };

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
    };
};

pub const Tree = struct {
    tag: Tree.Tag,
    children_pos: u32,
    children_len: u32,

    pub const Index = struct { index: u32 };

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

        stmt_block,
        stmt_expr,
        stmt_return,

        fn_params,
        fn_param,
        fn_returns,
        fn_return,

        struct_field,
    };
};

pub const Child = struct {
    node: Node.Index,
    tag: Node.Tag,
};

pub const Root = struct {
    tokens: std.MultiArrayList(Token) = .{},
    text: std.ArrayListUnmanaged(u8) = .{},
    trees: std.MultiArrayList(Tree) = .{},
    children: std.MultiArrayList(Child) = .{},

    pub fn deinit(root: *Root, allocator: std.mem.Allocator) void {
        root.tokens.deinit(allocator);
        root.text.deinit(allocator);
        root.trees.deinit(allocator);
        root.children.deinit(allocator);
    }

    // Token accessors

    pub fn tokenData(root: Root, id: Token.Index) Token {
        return root.tokens.get(id.index);
    }

    pub fn tokenTag(root: Root, id: Token.Index) Token.Tag {
        return root.tokenData(id).tag;
    }

    pub fn tokenText(root: Root, id: Token.Index) []const u8 {
        const data = root.tokenData(id);
        return root.text.items[data.text_pos .. data.text_pos + data.text_len];
    }

    // Tree accessors

    pub fn treeData(root: Root, id: Tree.Index) Tree {
        return root.trees.get(id.index);
    }

    pub fn treeTag(root: Root, id: Tree.Index) Tree.Tag {
        return root.treeData(id).tag;
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

    pub fn format(root: Root, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");
        if (root.trees.len > 0)
            try root.formatTree(Tree.Index{ .index = 0 }, 0, writer);
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
        }
        try writer.writeByteNTimes(' ', indent);
        try writer.writeAll(")\n");
    }

    pub fn formatToken(root: Root, id: Token.Index, indent: usize, writer: anytype) !void {
        const data = root.tokenData(id);
        const text = root.text.items[data.text_pos .. data.text_pos + data.text_len];
        try writer.writeByteNTimes(' ', indent);
        try writer.print("{s}(\"{}\")\n", .{ @tagName(data.tag), std.zig.fmtEscapes(text) });
    }
};

test Root {
    var root: Root = .{};
    defer root.deinit(std.testing.allocator);

    try root.text.append(std.testing.allocator, '1');

    const token_id = Token.Index{ .index = 0 };
    const token_data = Token{ .tag = .number, .text_pos = 0, .text_len = 1 };
    try root.tokens.append(std.testing.allocator, token_data);
    try std.testing.expectEqual(token_data, root.tokenData(token_id));
    try std.testing.expectEqual(Token.Tag.number, root.tokenTag(token_id));
    try std.testing.expectEqualSlices(u8, "1", root.tokenText(token_id));

    const tree_id = Tree.Index{ .index = @intCast(u32, root.trees.len) };
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
