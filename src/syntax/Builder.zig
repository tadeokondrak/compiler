const std = @import("std");
const syntax = @import("../syntax.zig");

const Builder = @This();

allocator: std.mem.Allocator,
events: std.ArrayListUnmanaged(Event) = .{},
oom: bool = false,

pub const Event = union(enum) {
    open: struct { tag: syntax.Tree.Tag },
    token: struct { tag: syntax.Token.Tag, text: []const u8 },
    close,
};

pub const Mark = struct {
    index: usize,

    pub const invalid = Mark{ .index = ~@as(usize, 0) };
};

pub fn deinit(builder: *Builder) void {
    builder.events.deinit(builder.allocator);
}

pub fn open(builder: *Builder) Mark {
    if (builder.oom) return Mark.invalid;
    const mark = Mark{ .index = builder.events.items.len };
    builder.events.append(builder.allocator, Event{ .open = .{ .tag = .invalid } }) catch {
        builder.oom = true;
    };
    return mark;
}

pub fn openBefore(builder: *Builder, mark: Mark) Mark {
    if (builder.oom) return Mark.invalid;
    builder.events.insert(builder.allocator, mark.index, Event{ .open = .{ .tag = .invalid } }) catch {
        builder.oom = true;
    };
    return mark;
}

pub fn close(builder: *Builder, mark: Mark, tag: syntax.Tree.Tag) void {
    if (builder.oom) return;
    builder.events.items[mark.index].open.tag = tag;
    builder.events.append(builder.allocator, Event.close) catch {
        builder.oom = true;
    };
}

pub fn token(builder: *Builder, tag: syntax.Token.Tag, text: []const u8) void {
    if (builder.oom) return;
    builder.events.append(builder.allocator, Event{ .token = .{ .tag = tag, .text = text } }) catch {
        builder.oom = true;
    };
}

pub fn build(builder: *Builder, tree_allocator: std.mem.Allocator) error{OutOfMemory}!syntax.Root {
    if (builder.oom) return error.OutOfMemory;

    var root: syntax.Root = .{};

    var stack = std.ArrayList(struct {
        tree_id: syntax.Tree.Index,
        tag: syntax.Tree.Tag,
        num_children: usize,
    }).init(builder.allocator);
    defer std.debug.assert(stack.items.len == 1);
    defer stack.deinit();

    var child_nodes = std.ArrayList(syntax.Node.Index).init(builder.allocator);
    defer std.debug.assert(child_nodes.items.len == 1);
    defer child_nodes.deinit();

    var child_tags = std.ArrayList(syntax.Node.Tag).init(builder.allocator);
    defer std.debug.assert(child_tags.items.len == 1);
    defer child_tags.deinit();

    try stack.append(.{ .tree_id = undefined, .tag = undefined, .num_children = 0 });
    defer std.debug.assert(stack.items[0].num_children == 1);

    for (builder.events.items) |event| {
        switch (event) {
            .open => |open_event| {
                const tree_id = syntax.Tree.Index{ .index = std.math.cast(u32, root.trees.len) orelse return error.OutOfMemory };
                try root.trees.append(tree_allocator, syntax.Tree{
                    .tag = open_event.tag,
                    .children_pos = undefined,
                    .children_len = 0,
                });
                try child_nodes.append(syntax.Node.Index.fromTree(tree_id));
                try child_tags.append(syntax.Node.Tag.fromTreeTag(open_event.tag));
                stack.items[stack.items.len - 1].num_children += 1;
                try stack.append(.{ .tree_id = tree_id, .tag = open_event.tag, .num_children = 0 });
            },
            .token => |token_event| {
                const text_pos = root.text.items.len;
                try root.text.appendSlice(tree_allocator, token_event.text);
                const token_pos = root.tokens.len;
                try root.tokens.append(tree_allocator, syntax.Token{
                    .tag = token_event.tag,
                    .text_pos = std.math.cast(u32, text_pos) orelse return error.OutOfMemory,
                    .text_len = std.math.cast(u32, token_event.text.len) orelse return error.OutOfMemory,
                });
                try child_nodes.append(syntax.Node.Index.fromTokenIndex(@intCast(u32, token_pos)));
                try child_tags.append(syntax.Node.Tag.fromTokenTag(token_event.tag));
                stack.items[stack.items.len - 1].num_children += 1;
            },
            .close => {
                const stack_element = stack.pop();
                root.trees.items(.children_pos)[stack_element.tree_id.index] =
                    std.math.cast(u32, root.children.len) orelse return error.OutOfMemory;
                root.trees.items(.children_len)[stack_element.tree_id.index] =
                    std.math.cast(u32, stack_element.num_children) orelse return error.OutOfMemory;
                const children_start = root.children.len;
                try root.children.ensureUnusedCapacity(tree_allocator, stack_element.num_children);
                root.children.len += stack_element.num_children;
                std.mem.copy(
                    syntax.Node.Index,
                    root.children.items(.node)[children_start..],
                    child_nodes.items[child_nodes.items.len - stack_element.num_children ..],
                );
                std.mem.copy(
                    syntax.Node.Tag,
                    root.children.items(.tag)[children_start..],
                    child_tags.items[child_tags.items.len - stack_element.num_children ..],
                );
                child_nodes.items.len -= stack_element.num_children;
                child_tags.items.len -= stack_element.num_children;
            },
        }
    }

    return root;
}

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
    ++ "\n", text);
}
