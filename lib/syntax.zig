const std = @import("std");

pub const pure = @import("syntax/pure.zig");

pub const Context = struct {
    arena: std.mem.Allocator,
    root: pure.Root,

    pub fn createTree(ctx: *Context, pure_tree: pure.Tree.Index) error{OutOfMemory}!*const Tree {
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

pub const Children = struct {
    tree: *const Tree,
    child_nodes: []const pure.Node.Index,
    child_tags: []const pure.Node.Tag,
    index: usize = 0,
    last_yielded: ?Node = null,

    pub fn next(iter: *Children) error{OutOfMemory}!?Node {
        if (iter.last_yielded) |last_yielded| last_yielded.deinit();
        if (iter.index >= iter.child_tags.len) return null;
        const child_node = iter.child_nodes[iter.index];
        const child_tag = iter.child_tags[iter.index];
        iter.index += 1;
        if (child_node.isTree()) {
            const child_tree = child_node.asTree().?;
            const child_tree_tag = child_tag.asTreeTag().?;
            const child = try iter.tree.context.arena.create(Tree);
            child.* = .{
                .tag = child_tree_tag,
                .index = child_tree,
                .context = iter.tree.context,
                .parent = iter.tree,
            };
            iter.last_yielded = .{ .tree = child };
            return .{ .tree = child };
        } else if (child_node.isToken()) {
            const child_token = child_node.asToken().?;
            const child_token_tag = child_tag.asTokenTag().?;
            const child = try iter.tree.context.arena.create(Token);
            child.* = .{
                .tag = child_token_tag,
                .index = child_token,
                .parent = iter.tree,
                .context = iter.tree.context,
            };
            iter.last_yielded = .{ .token = child };
            return .{ .token = child };
        } else {
            unreachable;
        }
    }
};

pub const Tree = struct {
    tag: pure.Tree.Tag,
    index: pure.Tree.Index,
    context: *Context,
    parent: ?*const Tree,

    pub fn deinit(tree: *Tree) void {
        tree.context.arena.destroy(tree);
    }

    pub fn format(tree: *const Tree, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        var iter = tree.children();
        for (iter.next() catch return) |child|
            try writer.print("{}", .{child});
    }

    pub fn children(tree: *const Tree) Children {
        return .{
            .tree = tree,
            .child_nodes = tree.context.root.treeChildren(tree.index),
            .child_tags = tree.context.root.treeChildrenTags(tree.index),
        };
    }

    pub fn span(tree: Tree) pure.Span {
        return tree.context.root.treeSpan(tree.index);
    }

    pub fn getTree(tree: *const Tree, tree_span: pure.Span) !?*const Tree {
        if (tree_span.start.offset == tree.span().start.offset and
            tree_span.end.offset == tree.span().end.offset)
        {
            return tree;
        }

        var iter = tree.children();
        while (try iter.next()) |child| {
            switch (child) {
                .tree => |child_tree| {
                    if (try child_tree.getTree(tree_span)) |found_tree|
                        return found_tree;
                },
                .token => {},
            }
        }

        return null;
    }

    pub fn getToken(tree: *const Tree, token_span: pure.Span) !?*Token {
        var iter = tree.children();
        while (try iter.next()) |child| {
            switch (child) {
                .tree => |child_tree| {
                    const token = try child_tree.getToken(span);
                    if (token != null) return token;
                },
                .token => |child_token| {
                    const child_token_span = child_token.span();
                    if (child_token_span.start.offset == token_span.offset and
                        token_span.offset == child_token_span.end.offset)
                        return child_token;
                },
            }
        }

        return null;
    }

    pub fn findToken(tree: *const Tree, pos: pure.Pos) !?*Token {
        var iter = tree.children();
        while (try iter.next()) |child| {
            switch (child) {
                .tree => |child_tree| {
                    const node = try child_tree.findToken(pos);
                    if (node != null) return node;
                },
                .token => |child_token| {
                    const token_span = child_token.spanWithTrivia();
                    if (pos.offset >= token_span.start.offset and
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

    pub fn deinit(token: *Token) void {
        token.context.arena.destroy(token);
    }

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

    pub fn text(token: Token) []const u8 {
        return token.context.root.tokenText(token.index);
    }

    pub fn span(token: Token) pure.Span {
        return token.context.root.tokenSpan(token.index);
    }

    pub fn spanWithTrivia(token: Token) pure.Span {
        const data = token.context.root.tokenData(token.index);
        var trivia_size: u32 = 0;
        for (data.trivia_start..data.trivia_start + data.trivia_count) |i| {
            const trivia = token.context.root.trivia.get(i);
            trivia_size += trivia.count;
        }
        return .{
            .start = .{ .offset = token.span().start.offset - trivia_size },
            .end = token.span().end,
        };
    }
};

pub const Node = union(enum) {
    tree: *Tree,
    token: *Token,

    pub fn deinit(node: Node) void {
        switch (node) {
            .tree => |tree| tree.deinit(),
            .token => |token| token.deinit(),
        }
    }

    pub fn format(node: Node, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (node) {
            .tree => |tree| try tree.format("", .{}, writer),
            .token => |token| try token.format("", .{}, writer),
        }
    }

    pub fn span(node: Node) pure.Span {
        switch (node) {
            .tree => |tree| return tree.span(),
            .token => |token| return token.span(),
        }
    }

    pub fn parent(node: Node) ?*const Tree {
        switch (node) {
            .tree => |tree| return tree.parent,
            .token => |token| return token.parent,
        }
    }
};

comptime {
    _ = pure;
}
