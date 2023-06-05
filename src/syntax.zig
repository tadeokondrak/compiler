//! Lossless homogenous syntax tree.
//!
//! See https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html for some context.

const std = @import("std");

pub const Builder = @import("syntax/Builder.zig");
pub const TreeTag = @import("syntax/tags.zig").TreeTag;
pub const TokenTag = @import("syntax/tags.zig").TokenTag;

comptime {
    _ = Builder;
    _ = TreeTag;
    _ = TokenTag;
}

pub const NodeTag = struct {
    bits: u16,

    const TREE_FLAG: u16 = 1 << 15;

    pub fn isTreeTag(tag: NodeTag) bool {
        //return (@enumToInt(tag) & TREE_FLAG) != 0;
        return tag.bits & TREE_FLAG != 0;
    }

    pub fn asTreeTag(tag: NodeTag) ?TreeTag {
        if (!isTreeTag(tag)) return null;
        return @intToEnum(TreeTag, tag.bits & ~TREE_FLAG);
    }

    pub fn fromTreeTag(tag: TreeTag) NodeTag {
        return NodeTag{ .bits = @as(u16, @enumToInt(tag)) | TREE_FLAG };
    }

    pub fn isTokenTag(tag: NodeTag) bool {
        return tag.bits & TREE_FLAG == 0;
    }

    pub fn asTokenTag(tag: NodeTag) ?TokenTag {
        if (!isTokenTag(tag)) return null;
        return @intToEnum(TokenTag, tag.bits);
    }

    pub fn fromTokenTag(tag: TokenTag) NodeTag {
        return NodeTag{ .bits = @enumToInt(tag) };
    }
};

pub const Tree = struct {
    index: u32,

    pub fn fromTreeIndex(index: u32) Tree {
        return Tree{ .bits = index };
    }
};

pub const Token = struct {
    index: u32,

    fn fromTokenIndex(index: u32) Token {
        return Token{ .bits = index };
    }
};

pub const Node = struct {
    bits: u32,

    const TREE_FLAG: u32 = 1 << 31;

    pub fn isTree(node: Node) bool {
        return (node.bits & TREE_FLAG) != 0;
    }

    pub fn asTree(node: Node) ?Tree {
        if (!isTree(node)) return null;
        return Tree{ .index = node.bits & ~TREE_FLAG };
    }

    pub fn fromTree(tree: Tree) Node {
        return Node{ .bits = tree.index | TREE_FLAG };
    }

    pub fn fromTreeIndex(id: u32) Node {
        return Node{ .bits = id | TREE_FLAG };
    }

    pub fn isToken(node: Node) bool {
        return (node.bits & TREE_FLAG) == 0;
    }

    pub fn asToken(node: Node) ?Token {
        if (!isToken(node)) return null;
        return Token{ .index = node.bits };
    }

    pub fn fromToken(token: Token) Node {
        return Node{ .bits = token.index };
    }

    pub fn fromTokenIndex(id: u32) Node {
        return Node{ .bits = id };
    }
};

pub const TokenData = struct {
    tag: TokenTag,
    text_pos: u32,
    text_len: u32,
};

pub const TreeData = struct {
    tag: TreeTag,
    children_pos: u32,
    children_len: u32,
};

pub const ChildData = struct {
    node: Node,
    tag: NodeTag,
};

pub const Root = struct {
    tokens: std.MultiArrayList(TokenData) = .{},
    text: std.ArrayListUnmanaged(u8) = .{},
    trees: std.MultiArrayList(TreeData) = .{},
    children: std.MultiArrayList(ChildData) = .{},

    pub fn deinit(root: *Root, allocator: std.mem.Allocator) void {
        root.tokens.deinit(allocator);
        root.text.deinit(allocator);
        root.trees.deinit(allocator);
        root.children.deinit(allocator);
    }

    // Token accessors

    pub fn tokenData(root: Root, id: Token) TokenData {
        return root.tokens.get(id.index);
    }

    pub fn tokenTag(root: Root, id: Token) TokenTag {
        return root.tokenData(id).tag;
    }

    pub fn tokenText(root: Root, id: Token) []const u8 {
        const data = root.tokenData(id);
        return root.text.items[data.text_pos .. data.text_pos + data.text_len];
    }

    // Tree accessors

    pub fn treeData(root: Root, id: Tree) TreeData {
        return root.trees.get(id.index);
    }

    pub fn treeTag(root: Root, id: Tree) TreeTag {
        return root.treeData(id).tag;
    }

    pub fn treeChildren(root: Root, id: Tree) []const Node {
        const data = root.treeData(id);
        return root.children.items(.node)[data.children_pos .. data.children_pos + data.children_len];
    }

    pub fn treeChildrenTags(root: Root, id: Tree) []const NodeTag {
        const data = root.treeData(id);
        return root.children.items(.tag)[data.children_pos .. data.children_pos + data.children_len];
    }

    // Formatting

    pub fn format(root: Root, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");
        if (root.trees.len > 0)
            try root.formatTree(Tree{ .index = 0 }, 0, writer);
    }

    pub fn formatTree(root: Root, id: Tree, indent: usize, writer: anytype) !void {
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

    pub fn formatToken(root: Root, id: Token, indent: usize, writer: anytype) !void {
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

    const token_id = Token{ .index = 0 };
    const token_data = TokenData{ .tag = .number, .text_pos = 0, .text_len = 1 };
    try root.tokens.append(std.testing.allocator, token_data);
    try std.testing.expectEqual(token_data, root.tokenData(token_id));
    try std.testing.expectEqual(TokenTag.number, root.tokenTag(token_id));
    try std.testing.expectEqualSlices(u8, "1", root.tokenText(token_id));

    const tree_id = Tree{ .index = @intCast(u32, root.trees.len) };
    const tree_data = TreeData{ .tag = .expr_literal, .children_pos = 0, .children_len = 1 };
    try root.trees.append(std.testing.allocator, tree_data);
    try root.children.append(std.testing.allocator, .{
        .node = Node.fromToken(token_id),
        .tag = NodeTag.fromTokenTag(token_data.tag),
    });
    try std.testing.expectEqual(tree_data, root.treeData(tree_id));
    try std.testing.expectEqual(TreeTag.expr_literal, root.treeTag(tree_id));
    try std.testing.expectEqualSlices(Node, &.{Node.fromToken(token_id)}, root.treeChildren(tree_id));
    try std.testing.expectEqual(@as(?Tree, null), root.treeChildren(tree_id)[0].asTree());
    try std.testing.expectEqual(@as(?Token, token_id), root.treeChildren(tree_id)[0].asToken());

    const text = try std.fmt.allocPrint(std.testing.allocator, "{}", .{root});
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualSlices(u8,
        \\expr_literal(
        \\  number("1")
        \\)
        \\
    , text);
}
