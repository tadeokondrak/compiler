const std = @import("std");
const ungrammar = @import("ungrammar");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{}) = .{};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();

    const src = try std.io.getStdIn().readToEndAlloc(allocator, std.math.maxInt(usize));
    defer allocator.free(src);

    var buffered_writer = std.io.bufferedWriter(std.io.getStdOut().writer());

    var result = try ungrammar.parse(allocator, src);
    defer result.deinit(allocator);

    const grammar = switch (result) {
        .success => |grammar| grammar,
        .failure => |failure| {
            try std.io.getStdErr().writer().print("{s}", .{failure.message});
            return;
        },
    };

    var ws = std.json.writeStream(buffered_writer.writer(), 256);
    ws.whitespace.indent = .none;
    ws.whitespace.separator = false;
    try emitGrammar(&ws, grammar);
    try buffered_writer.flush();
}

fn emitGrammar(ws: anytype, grammar: ungrammar.Grammar) !void {
    try ws.beginObject();
    for (0..grammar.nodes.len) |node_index| {
        const node: ungrammar.Node.Index = @enumFromInt(node_index);
        const name = grammar.nodeName(node);
        const rule = grammar.nodeRule(node);
        try ws.objectField(name);
        try emitRule(ws, grammar, rule);
    }
    try ws.endObject();
}

fn emitRule(ws: anytype, grammar: ungrammar.Grammar, rule: ungrammar.Rule.Index) !void {
    try ws.beginObject();
    switch (grammar.ruleTag(rule)) {
        .label => {
            const extra = grammar.ruleLabel(rule);
            const label = grammar.nullTerminatedString(extra.label_pos);
            try ws.objectField("label");
            try ws.emitString(label);
            try ws.objectField("rule");
            try emitRule(ws, grammar, extra.rule);
        },
        .node => {
            const data = grammar.ruleNode(rule);
            try ws.objectField("node");
            try ws.emitString(grammar.nodeName(data));
        },
        .token => {
            const data = grammar.ruleToken(rule);
            try ws.objectField("token");
            try ws.emitString(grammar.tokenName(data));
        },
        .seq, .alt => |tag| {
            const extra = grammar.ruleBin(rule);

            try ws.objectField(@tagName(tag));
            try ws.beginArray();

            try ws.arrayElem();
            try emitRule(ws, grammar, extra.lhs);

            var rhs = extra.rhs;
            while (grammar.ruleTag(rhs) == tag) {
                const rhs_extra = grammar.ruleBin(rhs);
                try ws.arrayElem();
                try emitRule(ws, grammar, rhs_extra.lhs);
                rhs = rhs_extra.rhs;
            }

            try ws.arrayElem();
            try emitRule(ws, grammar, rhs);

            try ws.endArray();
        },
        .opt => {
            const data = grammar.ruleRule(rule);
            try ws.objectField("opt");
            try emitRule(ws, grammar, data);
        },
        .rep => {
            const data = grammar.ruleRule(rule);
            try ws.objectField("rep");
            try emitRule(ws, grammar, data);
        },
    }
    try ws.endObject();
}
