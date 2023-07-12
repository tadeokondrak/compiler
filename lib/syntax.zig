const std = @import("std");

pub const ast = @import("syntax/ast.zig");
pub const pure = @import("syntax/pure.zig");

pub const Context = struct {
    arena: std.mem.Allocator,
    root: pure.Root,

    pub fn createTree(ctx: *Context, pure_tree: pure.Tree.Index) error{OutOfMemory}!*Tree {
        const tree = try ctx.arena.create(Tree);
        tree.* = .{
            .tag = ctx.root.treeTag(pure_tree),
            .index = pure_tree,
            .context = ctx,
            .parent = null,
        };
        return tree;
    }
};

pub const Tree = struct {
    tag: pure.Tree.Tag,
    index: pure.Tree.Index,
    context: *Context,
    parent: ?*const Tree,

    pub fn format(tree: Tree, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        for (tree.children() catch return) |child|
            try writer.print("{}", .{child});
    }

    pub fn children(tree: *const Tree) error{OutOfMemory}![]Node {
        const child_nodes = tree.context.root.treeChildren(tree.index);
        const child_tags = tree.context.root.treeChildrenTags(tree.index);
        const nodes = try tree.context.arena.alloc(Node, child_nodes.len);
        errdefer tree.context.arena.free(nodes);
        for (0.., child_nodes, child_tags) |i, child_node, child_tag| {
            if (child_node.isTree()) {
                const child_tree = child_node.asTree().?;
                const child_tree_tag = child_tag.asTreeTag().?;
                const child = try tree.context.arena.create(Tree);
                child.* = .{
                    .tag = child_tree_tag,
                    .index = child_tree,
                    .context = tree.context,
                    .parent = tree,
                };
                nodes[i] = .{ .tree = child };
            } else if (child_node.isToken()) {
                const child_token = child_node.asToken().?;
                const child_token_tag = child_tag.asTokenTag().?;
                const child = try tree.context.arena.create(Token);
                child.* = .{
                    .tag = child_token_tag,
                    .index = child_token,
                    .parent = tree,
                    .context = tree.context,
                };
                nodes[i] = .{ .token = child };
            } else {
                unreachable;
            }
        }
        return nodes;
    }

    pub fn span(tree: Tree) pure.Span {
        return tree.context.root.treeSpan(tree.index);
    }

    pub fn findToken(tree: *const Tree, pos: pure.Pos) !?*Token {
        for (try tree.children()) |child| {
            switch (child) {
                .tree => |child_tree| {
                    const token = try child_tree.findToken(pos);
                    if (token != null) return token;
                },
                .token => |child_token| {
                    const token_span = child_token.span();
                    if (token_span.start.offset <= pos.offset and
                        pos.offset < token_span.end.offset)
                        return child_token;
                },
            }
        }

        return null;
    }
};

pub const Token = struct {
    tag: pure.Token.Tag,
    index: pure.Token.Index,
    parent: *const Tree,
    context: *Context,

    pub fn format(token: Token, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        const data = token.context.root.tokenData(token.index);
        if (data.trivia_count != 0) {
            for (data.trivia_start..data.trivia_start + data.trivia_count) |i| {
                const trivia = token.context.root.trivia.get(i);
                const byte: u8 = switch (trivia.tag) {
                    .tab => '\t',
                    .space => ' ',
                    .newline => '\n',
                    .carriage_return => '\r',
                };
                try writer.writeByteNTimes(byte, trivia.count);
            }
        }
        try writer.print("{s}", .{token.context.root.text.items[data.text_pos..][0..data.text_len]});
    }

    pub fn span(token: Token) pure.Span {
        return token.context.root.tokenSpan(token.index);
    }
};

const Node = union(enum) {
    tree: *Tree,
    token: *Token,

    pub fn format(node: Node, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (node) {
            .tree => |tree| try tree.format("", .{}, writer),
            .token => |token| try token.format("", .{}, writer),
        }
    }
};

comptime {
    _ = ast;
    _ = pure;
}
