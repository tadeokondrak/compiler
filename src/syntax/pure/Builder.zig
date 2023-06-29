const std = @import("std");
const syntax = @import("../../syntax.zig");

const Builder = @This();

allocator: std.mem.Allocator,
events: std.ArrayListUnmanaged(Event) = .{},
oom: bool = false,

pub const Event = union(enum) {
    open: struct { tag: syntax.pure.Tree.Tag },
    token: struct { tag: syntax.pure.Token.Tag },
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

pub fn close(builder: *Builder, mark: Mark, tag: syntax.pure.Tree.Tag) void {
    if (builder.oom) return;
    builder.events.items[mark.index].open.tag = tag;
    builder.events.append(builder.allocator, Event.close) catch {
        builder.oom = true;
    };
}

pub fn token(builder: *Builder, tag: syntax.pure.Token.Tag) void {
    if (builder.oom) return;
    builder.events.append(builder.allocator, Event{ .token = .{ .tag = tag } }) catch {
        builder.oom = true;
    };
}

fn appendTrivia(allocator: std.mem.Allocator, trivia: *std.MultiArrayList(syntax.pure.Trivia), text: []const u8) error{OutOfMemory}!u32 {
    var i: usize = 0;
    var trivia_count: u32 = 0;
    while (i < text.len) {
        var count: u8 = 0;
        const c = text[i];
        while (count < std.math.maxInt(u8) and i < text.len and text[i] == c) {
            count += 1;
            i += 1;
        }
        try trivia.append(allocator, syntax.pure.Trivia{
            .tag = switch (c) {
                '\t' => .tab,
                ' ' => .space,
                '\n' => .newline,
                '\r' => .carriage_return,
                else => unreachable,
            },
            .count = count,
        });
        trivia_count += 1;
    }
    return trivia_count;
}

pub fn build(
    builder: *Builder,
    tree_allocator: std.mem.Allocator,
    text: []const u8,
    tokens: []syntax.pure.Token.Tag,
    lengths: []usize,
) error{OutOfMemory}!syntax.pure.Root {
    if (builder.oom) return error.OutOfMemory;

    var root: syntax.pure.Root = .{};

    var stack = std.ArrayListUnmanaged(struct {
        tree_id: syntax.pure.Tree.Index,
        tag: syntax.pure.Tree.Tag,
        num_children: usize,
    }){};
    defer stack.deinit(builder.allocator);
    defer std.debug.assert(stack.items.len == 1);

    var child_nodes = std.ArrayListUnmanaged(syntax.pure.Node.Index){};
    defer child_nodes.deinit(builder.allocator);
    defer std.debug.assert(child_nodes.items.len == 1);

    var child_tags = std.ArrayListUnmanaged(syntax.pure.Node.Tag){};
    defer child_tags.deinit(builder.allocator);
    defer std.debug.assert(child_tags.items.len == 1);

    try stack.append(builder.allocator, .{ .tree_id = undefined, .tag = undefined, .num_children = 0 });
    defer std.debug.assert(stack.items[0].num_children == 1);

    var token_pos: usize = 0;
    defer std.debug.assert(token_pos == tokens.len);

    var text_pos: usize = 0;
    defer std.debug.assert(text_pos == text.len);

    var pending_trivia_start: usize = undefined;
    var pending_trivia_count: usize = 0;

    for (builder.events.items) |event| switch (event) {
        .open => |open_event| {
            const tree_id = @intToEnum(syntax.pure.Tree.Index, std.math.cast(u32, root.trees.len) orelse return error.OutOfMemory);
            try root.trees.append(tree_allocator, syntax.pure.Tree{
                .tag = open_event.tag,
                .children_pos = undefined,
                .children_len = 0,
            });
            try child_nodes.append(builder.allocator, syntax.pure.Node.Index.fromTree(tree_id));
            try child_tags.append(builder.allocator, syntax.pure.Node.Tag.fromTreeTag(open_event.tag));
            stack.items[stack.items.len - 1].num_children += 1;
            try stack.append(builder.allocator, .{ .tree_id = tree_id, .tag = open_event.tag, .num_children = 0 });

            if (stack.items.len == 2) {
                // Top level, eat whitespace
                while (token_pos < tokens.len and tokens[token_pos] == .space) {
                    const trivia_text_len = lengths[token_pos];
                    const trivia_text = text[text_pos..][0..trivia_text_len];
                    if (pending_trivia_count == 0)
                        pending_trivia_start = root.trivia.len;
                    // TODO handle overflow
                    pending_trivia_count += try appendTrivia(tree_allocator, &root.trivia, trivia_text);
                    text_pos += lengths[token_pos];
                    token_pos += 1;
                }
            }
        },
        .token => |token_event| {
            // Eat whitespace
            var trivia_count: usize = pending_trivia_count;
            const trivia_start = if (trivia_count > 0) pending_trivia_start else root.trivia.len;
            pending_trivia_start = undefined;
            pending_trivia_count = 0;
            while (token_pos < tokens.len and tokens[token_pos] == .space) {
                const trivia_text_len = lengths[token_pos];
                const trivia_text = text[text_pos..][0..trivia_text_len];
                // TODO handle overflow
                trivia_count += try appendTrivia(tree_allocator, &root.trivia, trivia_text);
                text_pos += lengths[token_pos];
                token_pos += 1;
            }

            const token_text_len = lengths[token_pos];
            const token_text = text[text_pos..][0..token_text_len];
            text_pos += token_text_len;
            token_pos += 1;

            const root_text_pos = root.text.items.len;
            try root.text.appendSlice(tree_allocator, token_text);

            const root_token_pos = root.tokens.len;
            try root.tokens.append(tree_allocator, syntax.pure.Token{
                .tag = token_event.tag,
                .text_pos = root_text_pos,
                .text_len = token_text_len,
                .trivia_start = trivia_start,
                .trivia_count = trivia_count,
            });

            try child_nodes.append(builder.allocator, syntax.pure.Node.Index.fromTokenIndex(@intCast(u32, root_token_pos)));
            try child_tags.append(builder.allocator, syntax.pure.Node.Tag.fromTokenTag(token_event.tag));
            stack.items[stack.items.len - 1].num_children += 1;
        },
        .close => {
            if (stack.items.len == 2) {
                var trivia_count: usize = pending_trivia_count;
                const trivia_start = if (trivia_count > 0) pending_trivia_start else root.trivia.len;
                while (token_pos < tokens.len and tokens[token_pos] == .space) {
                    const trivia_text_len = lengths[token_pos];
                    const trivia_text = text[text_pos..][0..trivia_text_len];
                    // TODO handle overflow
                    trivia_count += try appendTrivia(tree_allocator, &root.trivia, trivia_text);
                    text_pos += lengths[token_pos];
                    token_pos += 1;
                }

                // Inject EOF token
                const root_token_pos = root.tokens.len;
                try root.tokens.append(tree_allocator, syntax.pure.Token{
                    .tag = .eof,
                    .text_pos = 0,
                    .text_len = 0,
                    .trivia_start = trivia_start,
                    .trivia_count = trivia_count,
                });

                try child_nodes.append(builder.allocator, syntax.pure.Node.Index.fromTokenIndex(@intCast(u32, root_token_pos)));
                try child_tags.append(builder.allocator, syntax.pure.Node.Tag.fromTokenTag(.eof));
                stack.items[stack.items.len - 1].num_children += 1;
            }

            const stack_element = stack.pop();
            root.trees.items(.children_pos)[@enumToInt(stack_element.tree_id)] =
                std.math.cast(u32, root.children.len) orelse return error.OutOfMemory;
            root.trees.items(.children_len)[@enumToInt(stack_element.tree_id)] =
                std.math.cast(u32, stack_element.num_children) orelse return error.OutOfMemory;
            const children_start = root.children.len;
            try root.children.ensureUnusedCapacity(tree_allocator, stack_element.num_children);
            root.children.len += stack_element.num_children;
            std.mem.copy(
                syntax.pure.Node.Index,
                root.children.items(.node)[children_start..],
                child_nodes.items[child_nodes.items.len - stack_element.num_children ..],
            );
            std.mem.copy(
                syntax.pure.Node.Tag,
                root.children.items(.tag)[children_start..],
                child_tags.items[child_tags.items.len - stack_element.num_children ..],
            );
            child_nodes.items.len -= stack_element.num_children;
            child_tags.items.len -= stack_element.num_children;
        },
    };

    return root;
}
