//! Lossless homogenous syntax tree.
//!
//! See https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html for some context.

const std = @import("std");

pub const TreeTag = @import("syntax/tags.zig").TreeTag;
pub const TokenTag = @import("syntax/tags.zig").TokenTag;

pub const NodeTag = enum(u16) {
    _,

    const TREE_FLAG: u16 = 1 << 15;

    pub fn isTreeTag(tag: NodeTag) bool {
        return (@enumToInt(tag) & TREE_FLAG) != 0;
    }

    pub fn asTreeTag(tag: NodeTag) ?TreeTag {
        return if (isTreeTag(tag)) @intToEnum(TreeTag, @as(u16, @enumToInt(tag)) & ~TREE_FLAG) else null;
    }

    pub fn fromTreeTag(tag: TreeTag) NodeTag {
        return @intToEnum(NodeTag, @as(u16, @enumToInt(tag)) | TREE_FLAG);
    }

    pub fn isTokenTag(tag: NodeTag) bool {
        return (@enumToInt(tag) & TREE_FLAG) == 0;
    }

    pub fn asTokenTag(tag: NodeTag) ?TokenTag {
        return if (isTokenTag(tag)) @intToEnum(TokenTag, @as(u16, @enumToInt(tag))) else null;
    }

    pub fn fromTokenTag(tag: TokenTag) NodeTag {
        return @intToEnum(NodeTag, @as(u16, @enumToInt(tag)));
    }
};

pub const Tree = enum(u31) {
    _,

    pub fn fromTreeIndex(index: u32) Tree {
        return @intToEnum(Tree, index);
    }
};

pub const Token = enum(u31) {
    _,

    fn fromTokenIndex(index: u32) Token {
        return @intToEnum(Token, index);
    }
};

pub const Node = enum(u32) {
    _,

    const TREE_FLAG: u32 = 1 << 31;

    pub fn isTree(node: Node) bool {
        return (@enumToInt(node) & TREE_FLAG) != 0;
    }

    pub fn asTree(node: Node) ?Tree {
        return if (isTree(node)) @intToEnum(Tree, @as(u32, @enumToInt(node)) & ~TREE_FLAG) else null;
    }

    pub fn fromTree(id: Tree) Node {
        return @intToEnum(Node, @as(u32, @enumToInt(id)) | TREE_FLAG);
    }

    pub fn fromTreeIndex(id: u32) Node {
        return @intToEnum(Node, id | TREE_FLAG);
    }

    pub fn isToken(node: Node) bool {
        return (@enumToInt(node) & TREE_FLAG) == 0;
    }

    pub fn asToken(node: Node) ?Token {
        return if (isToken(node)) @intToEnum(Token, @as(u32, @enumToInt(node))) else null;
    }

    pub fn fromToken(id: Token) Node {
        return @intToEnum(Node, @as(u32, @enumToInt(id)));
    }

    pub fn fromTokenIndex(id: u32) Node {
        return @intToEnum(Node, id);
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
        return root.tokens.get(@enumToInt(id));
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
        return root.trees.get(@enumToInt(id));
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
            try root.formatTree(@intToEnum(Tree, 0), 0, writer);
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

    const token_id = @intToEnum(Token, root.tokens.len);
    const token_data = TokenData{ .tag = .number, .text_pos = 0, .text_len = 1 };
    try root.tokens.append(std.testing.allocator, token_data);
    try std.testing.expectEqual(token_data, root.tokenData(token_id));
    try std.testing.expectEqual(TokenTag.number, root.tokenTag(token_id));
    try std.testing.expectEqualSlices(u8, "1", root.tokenText(token_id));

    const tree_id = @intToEnum(Tree, root.trees.len);
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

pub const Builder = @import("syntax/Builder.zig");

test Builder {
    const allocator = std.heap.page_allocator;
    var builder = Builder{ .allocator = allocator };
    const mark = builder.open();
    builder.token(.ident, "foo");
    builder.close(mark, .expr_ident);

    var root = try builder.build(std.testing.allocator);
    defer root.deinit(std.testing.allocator);

    const text = try std.fmt.allocPrint(std.testing.allocator, "{}", .{root});
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualSlices(u8,
        \\expr_ident(
        \\  ident("foo")
        \\)
        \\
    , text);
}

pub fn castTree(root: Root, tree: Tree, tag: TreeTag, comptime T: type) ?T {
    if (root.treeTag(tree) != tag) return null;
    return T{ .tree = tree };
}

pub fn findNthTree(root: Root, tree: Tree, comptime T: type, comptime n: usize) ?T {
    var i: usize = 0;
    for (root.treeChildren(tree)) |child| {
        if (child.asTree()) |child_tree| {
            if (T.cast(root, child_tree)) |casted_tree| {
                if (i == n)
                    return casted_tree
                else
                    i += 1;
            }
        }
    }
    return null;
}

pub fn findTree(root: Root, tree: Tree, comptime T: type) ?T {
    return findNthTree(root, tree, T, 0);
}

pub fn findToken(root: Root, tree: Tree, tag: TokenTag) ?Token {
    for (root.treeChildren(tree), root.treeChildrenTags(tree)) |child, child_tag|
        if (child_tag.asTokenTag() == tag)
            return child.asToken().?;
    return null;
}
