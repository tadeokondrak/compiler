const std = @import("std");
const ungrammar = @import("ungrammar");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{}) = .{};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();

    if (std.os.argv.len != 3) {
        try std.io.getStdErr().writer().writeAll("need in and out arguments\n");
        return;
    }

    const in_path = std.os.argv[1];
    const out_path = std.os.argv[2];

    const in = try std.fs.cwd().openFileZ(in_path, .{});
    defer in.close();

    const out = try std.fs.cwd().createFileZ(out_path, .{});
    defer out.close();

    const src = try in.readToEndAlloc(allocator, std.math.maxInt(usize));
    defer allocator.free(src);

    var buffered_writer = std.io.bufferedWriter(out.writer());

    var result = try ungrammar.parse(allocator, src);
    defer result.deinit(allocator);

    const grammar = switch (result) {
        .success => |grammar| grammar,
        .failure => |failure| {
            try std.io.getStdErr().writer().print("{s}", .{failure.message});
            return;
        },
    };

    try buffered_writer.writer().writeAll(
        \\const std = @import("std");
        \\const syntax = @import("syntax");
        \\
        \\const ast = @This();
        \\
        \\comptime {
        \\    std.testing.refAllDeclsRecursive(ast);
        \\}
        \\
        \\pub fn Ptr(comptime T: type) type {
        \\    return struct {
        \\        span: syntax.pure.Span,
        \\
        \\        pub fn deref(ptr: @This(), tree: *const syntax.Tree) !T {
        \\            const found = try tree.getTree(ptr.span);
        \\            return T.cast(found.?).?;
        \\        }
        \\    };
        \\}
        \\
        \\pub fn TreeIterator(comptime T: type) type {
        \\    return struct {
        \\        nodes: []syntax.Node,
        \\
        \\        pub fn next(this: *@This()) ?T {
        \\            for (this.nodes, 0..) |node, i| {
        \\                switch (node) {
        \\                    .tree => |tree| {
        \\                        if (T.cast(tree)) |correct_tree| {
        \\                            this.nodes = this.nodes[i + 1 ..];
        \\                            return correct_tree;
        \\                        }
        \\                    },
        \\                    .token => {},
        \\                }
        \\            }
        \\            return null;
        \\        }
        \\    };
        \\}
        \\
    );

    try emitGrammar(buffered_writer.writer(), grammar, allocator);
    try buffered_writer.flush();
}

fn emitGrammar(ws: anytype, grammar: ungrammar.Grammar, allocator: std.mem.Allocator) !void {
    for (0..grammar.nodes.len) |node_index| {
        const node: ungrammar.Node.Index = @enumFromInt(node_index);
        const name = grammar.nodeName(node);
        const rule = grammar.nodeRule(node);
        try ws.print("pub const {s} = ", .{name});
        switch (grammar.ruleTag(rule)) {
            .alt => {
                try ws.writeAll(
                    \\union(enum) {
                    \\
                );
                const extra = grammar.ruleBin(rule);
                try emitUnionMember(ws, grammar, extra.lhs);
                var rhs = extra.rhs;
                while (grammar.ruleTag(rhs) == .alt) {
                    const rhs_extra = grammar.ruleBin(rhs);
                    try emitUnionMember(ws, grammar, rhs_extra.lhs);
                    rhs = rhs_extra.rhs;
                }
                try emitUnionMember(ws, grammar, rhs);
                try ws.writeAll(
                    \\
                    \\    pub fn cast(syntax_tree: *const syntax.Tree) ?@This() {
                    \\        inline for (@typeInfo(@This()).Union.fields) |field|
                    \\            if (field.type.cast(syntax_tree)) |correct_tree|
                    \\                return @unionInit(@This(), field.name, correct_tree);
                    \\        return null;
                    \\    }
                    \\
                    \\    pub fn tree(this: @This()) *const syntax.Tree {
                    \\        return switch (this) {
                    \\            inline else => |variant| variant.tree,
                    \\        };
                    \\    }
                    \\
                    \\    pub fn ptr(this: @This()) Ptr(@This()) {
                    \\        return .{ .span = this.span() };
                    \\    }
                    \\
                    \\    pub fn span(this: @This()) syntax.pure.Span {
                    \\        return switch (this) {
                    \\            inline else => |variant| variant.span(),
                    \\        };
                    \\    }
                    \\};
                    \\
                    \\
                );
            },
            else => {
                try ws.writeAll(
                    \\struct {
                    \\    tree: *const syntax.Tree,
                    \\
                );

                try ws.print(
                    \\
                    \\    pub const tag: syntax.pure.Tree.Tag = .{};
                    \\
                ,
                    .{fmtSnake(name)},
                );

                try ws.writeAll(
                    \\
                    \\    pub fn ptr(this: @This()) Ptr(@This()) {
                    \\        return .{ .span = this.tree.span() };
                    \\    }
                    \\
                    \\    pub fn span(this: @This()) syntax.pure.Span {
                    \\        return this.tree.span();
                    \\    }
                    \\
                    \\    pub fn cast(tree: *const syntax.Tree) ?@This() {
                    \\        if (tree.tag != tag) return null;
                    \\        return @This(){ .tree = tree };
                    \\    }
                    \\
                    \\    pub fn format(this: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
                    \\        try writer.writeAll(@tagName(tag) ++ "(");
                    \\        try writer.print("{}", .{this.tree});
                    \\        try writer.writeAll(")");
                    \\    }
                    \\
                    \\
                );
                var counts = std.StringHashMap(u8).init(allocator);
                defer counts.deinit();
                try emitStructMethod(ws, grammar, rule, &counts);
                try ws.writeAll("};\n\n");
            },
        }
    }
}

fn emitUnionMemberWithName(ws: anytype, grammar: ungrammar.Grammar, name: []const u8, rule: ungrammar.Rule.Index) !void {
    switch (grammar.ruleTag(rule)) {
        .node => {
            const data = grammar.ruleNode(rule);
            const node_name = grammar.nodeName(data);
            try ws.print("    @\"{}\": {s},\n", .{ fmtSnake(name), node_name });
        },
        else => |tag| std.debug.panic("unhandled: {s}", .{@tagName(tag)}),
    }
}

fn emitUnionMember(ws: anytype, grammar: ungrammar.Grammar, rule: ungrammar.Rule.Index) !void {
    switch (grammar.ruleTag(rule)) {
        .node => {
            const data = grammar.ruleNode(rule);
            const name = grammar.nodeName(data);
            return emitUnionMemberWithName(ws, grammar, name, rule);
        },
        .label => {
            const extra = grammar.ruleLabel(rule);
            const label = grammar.nullTerminatedString(extra.label_pos);
            return emitUnionMemberWithName(ws, grammar, label, extra.rule);
        },
        else => |tag| std.debug.panic("unhandled: {s}", .{@tagName(tag)}),
    }
}

fn emitStructMethodWithName(ws: anytype, grammar: ungrammar.Grammar, name: []const u8, rule: ungrammar.Rule.Index, counts: *std.StringHashMap(u8)) !void {
    switch (grammar.ruleTag(rule)) {
        .label => @panic("can't handle double-labeled rule"),
        .seq, .alt => @panic("can't handle labeled seq or alt"),
        .node => {
            const data = grammar.ruleNode(rule);
            const node_name = grammar.nodeName(data);
            try ws.print("    pub fn {}Node(this: @This()) error{{OutOfMemory}}!?{s} {{\n", .{
                fmtLowerCamel(name),
                node_name,
            });
            const result = try counts.getOrPut(node_name);
            if (!result.found_existing)
                result.value_ptr.* = 0;
            try ws.print(
                \\        var i: usize = 0;
                \\        for (try this.tree.children()) |child| {{
                \\            switch (child) {{
                \\                .tree => |child_tree| {{
                \\                    if ({s}.cast(child_tree)) |correct_tree| {{
                \\                        if (i == {})
                \\                            return correct_tree
                \\                        else
                \\                            i += 1;
                \\                    }}
                \\                }},
                \\                .token => {{}},
                \\            }}
                \\        }}
                \\        return null;
                \\    }}
                \\
                \\
            , .{ node_name, result.value_ptr.* });
            result.value_ptr.* += 1;
        },
        .token => {
            try ws.print("    pub fn {}Token(this: @This()) error{{OutOfMemory}}!?*syntax.Token {{\n", .{
                fmtLowerCamel(stripKwPrefix(tokenName(name))),
            });
            try ws.print(
                \\        for (try this.tree.children()) |child| {{
                \\            switch (child) {{
                \\                .tree => {{}},
                \\                .token => |token| {{
                \\                    if (token.tag == .{s})
                \\                        return token;
                \\                }},
                \\            }}
                \\        }}
                \\        return null;
                \\    }}
                \\
                \\
            , .{tokenName(name)});
        },
        .opt => {
            const data = grammar.ruleRule(rule);
            try emitStructMethodWithName(ws, grammar, name, data, counts);
        },
        .rep => {
            const data = grammar.ruleRule(rule);
            if (grammar.ruleTag(data) != .node) {
                @panic("can't handle rep of non-node");
            }
            const node = grammar.ruleNode(data);
            const node_name = grammar.nodeName(node);
            try ws.print("    pub fn {}Nodes(this: @This()) error{{OutOfMemory}}!TreeIterator({s}) {{\n", .{
                fmtLowerCamel(name),
                node_name,
            });
            try ws.writeAll(
                \\        return .{ .nodes = try this.tree.children() };
                \\    }
                \\
                \\
            );
        },
    }
}

fn inferRuleName(grammar: ungrammar.Grammar, rule: ungrammar.Rule.Index) []const u8 {
    switch (grammar.ruleTag(rule)) {
        .label => {
            const extra = grammar.ruleLabel(rule);
            return grammar.nullTerminatedString(extra.label_pos);
        },
        .node => {
            const data = grammar.ruleNode(rule);
            return grammar.nodeName(data);
        },
        .token => {
            const data = grammar.ruleToken(rule);
            return grammar.tokenName(data);
        },
        .seq, .alt => @panic("can't infer name for seq or alt"),
        .opt, .rep => {
            const data = grammar.ruleRule(rule);
            return inferRuleName(grammar, data);
        },
    }
}

fn emitStructMethod(ws: anytype, grammar: ungrammar.Grammar, rule: ungrammar.Rule.Index, counts: *std.StringHashMap(u8)) !void {
    switch (grammar.ruleTag(rule)) {
        .label => {
            const extra = grammar.ruleLabel(rule);
            const label = grammar.nullTerminatedString(extra.label_pos);
            try emitStructMethodWithName(ws, grammar, label, extra.rule, counts);
        },
        .node => {
            const data = grammar.ruleNode(rule);
            const name = grammar.nodeName(data);
            try emitStructMethodWithName(ws, grammar, name, rule, counts);
        },
        .token => {
            const data = grammar.ruleToken(rule);
            const name = grammar.tokenName(data);
            try emitStructMethodWithName(ws, grammar, name, rule, counts);
        },
        .seq, .alt => |tag| {
            const extra = grammar.ruleBin(rule);
            try emitStructMethod(ws, grammar, extra.lhs, counts);
            var rhs = extra.rhs;
            while (grammar.ruleTag(rhs) == tag) {
                const rhs_extra = grammar.ruleBin(rhs);
                try emitStructMethod(ws, grammar, rhs_extra.lhs, counts);
                rhs = rhs_extra.rhs;
            }
            try emitStructMethod(ws, grammar, rhs, counts);
        },
        .opt, .rep => {
            const name = inferRuleName(grammar, rule);
            try emitStructMethodWithName(ws, grammar, name, rule, counts);
        },
    }
}

fn formatSnake(s: []const u8, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
    for (s, 0..) |c, i| {
        if (std.ascii.isUpper(c) and i > 0)
            try writer.writeByte('_');
        try writer.writeByte(std.ascii.toLower(c));
    }
}

fn fmtSnake(s: []const u8) std.fmt.Formatter(formatSnake) {
    return .{ .data = s };
}

fn formatLowerCamel(s: []const u8, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
    if (s.len == 0) return;

    try writer.writeByte(std.ascii.toLower(s[0]));
    var upper = false;
    for (s[1..]) |c| {
        if (c == '_') {
            upper = true;
            continue;
        }
        try writer.writeByte(if (upper) std.ascii.toUpper(c) else c);
        upper = false;
    }
}

fn fmtLowerCamel(s: []const u8) std.fmt.Formatter(formatLowerCamel) {
    return .{ .data = s };
}

fn stripKwPrefix(s: []const u8) []const u8 {
    if (std.mem.startsWith(u8, s, "kw_"))
        return s[3..];
    return s;
}

fn tokenName(s: []const u8) []const u8 {
    const map = std.ComptimeStringMap([]const u8, .{
        .{ "(", "l_paren" },
        .{ ")", "r_paren" },
        .{ "[", "l_bracket" },
        .{ "]", "r_bracket" },
        .{ "{", "l_brace" },
        .{ "}", "r_brace" },
        .{ "+", "plus" },
        .{ "-", "minus" },
        .{ "*", "star" },
        .{ "/", "slash" },
        .{ "%", "percent" },
        .{ "&", "ampersand" },
        .{ "^", "caret" },
        .{ "|", "pipe" },
        .{ ";", "semi" },
        .{ ":", "colon" },
        .{ ",", "comma" },
        .{ ".", "dot" },
        .{ "!", "bang" },
        .{ "!=", "bang_eq" },
        .{ "=", "eq" },
        .{ "==", "eq2" },
        .{ "<", "lt" },
        .{ "<<", "lt2" },
        .{ "<=", "lt_eq" },
        .{ ">", "gt" },
        .{ ">>", "gt2" },
        .{ ">=", "gt_eq" },
        .{ "fn", "kw_fn" },
        .{ "return", "kw_return" },
        .{ "struct", "kw_struct" },
        .{ "const", "kw_const" },
        .{ "if", "kw_if" },
        .{ "else", "kw_else" },
        .{ "loop", "kw_loop" },
        .{ "while", "kw_while" },
        .{ "break", "kw_break" },
        .{ "continue", "kw_continue" },
        .{ "mut", "kw_mut" },
        .{ "let", "kw_let" },
        .{ "ident", "ident" },
        .{ "string", "string" },
        .{ "number", "number" },
    });
    return map.get(s) orelse @panic(s);
}
