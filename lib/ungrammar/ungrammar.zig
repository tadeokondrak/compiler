const std = @import("std");
const parser = @import("parser.zig");

pub const ParseResult = parser.ParseResult;
pub const parse = parser.parse;

pub const Grammar = struct {
    text: []u8,
    extra: []u32,
    tokens: []Token,
    nodes: std.MultiArrayList(Node).Slice,
    rules: std.MultiArrayList(Rule).Slice,

    pub fn deinit(grammar: *Grammar, allocator: std.mem.Allocator) void {
        allocator.free(grammar.text);
        allocator.free(grammar.extra);
        allocator.free(grammar.tokens);
        grammar.nodes.deinit(allocator);
        grammar.rules.deinit(allocator);
    }

    pub fn tokenName(grammar: Grammar, index: Token.Index) []const u8 {
        return grammar.nullTerminatedString(
            grammar.tokens[@intFromEnum(index)].name_pos,
        );
    }

    pub fn nodeName(grammar: Grammar, index: Node.Index) []const u8 {
        return grammar.nullTerminatedString(
            grammar.nodes.items(.name_pos)[@intFromEnum(index)],
        );
    }

    pub fn nodeRule(grammar: Grammar, index: Node.Index) Rule.Index {
        return grammar.nodes.items(.rule)[@intFromEnum(index)];
    }

    pub fn ruleTag(grammar: Grammar, index: Rule.Index) Rule.Tag {
        return grammar.rules.items(.tag)[@intFromEnum(index)];
    }

    pub fn ruleNode(grammar: Grammar, index: Rule.Index) Node.Index {
        std.debug.assert(grammar.ruleTag(index) == .node);
        return grammar.ruleData(index).node;
    }

    pub fn ruleToken(grammar: Grammar, index: Rule.Index) Token.Index {
        std.debug.assert(grammar.ruleTag(index) == .token);
        return grammar.ruleData(index).token;
    }

    pub fn ruleRule(grammar: Grammar, index: Rule.Index) Rule.Index {
        std.debug.assert(grammar.ruleTag(index) == .opt or grammar.ruleTag(index) == .rep);
        return grammar.ruleData(index).rule;
    }

    pub fn ruleLabel(grammar: Grammar, index: Rule.Index) Rule.Label {
        std.debug.assert(grammar.ruleTag(index) == .label);
        const extra = grammar.ruleData(index).extra;
        return grammar.extraData(Rule.Label, extra).data;
    }

    pub fn ruleBin(grammar: Grammar, index: Rule.Index) Rule.Bin {
        std.debug.assert(grammar.ruleTag(index) == .seq or grammar.ruleTag(index) == .alt);
        const extra = grammar.ruleData(index).extra;
        return grammar.extraData(Rule.Bin, extra).data;
    }

    fn ruleData(grammar: Grammar, index: Rule.Index) Rule.Data {
        return grammar.rules.items(.data)[@intFromEnum(index)];
    }

    fn ExtraData(comptime T: type) type {
        return struct { data: T, end: usize };
    }

    fn extraData(grammar: Grammar, comptime T: type, index: usize) ExtraData(T) {
        const fields = std.meta.fields(T);
        var i: usize = index;
        var result: T = undefined;
        inline for (fields) |field| {
            @field(result, field.name) = switch (field.type) {
                u32 => grammar.extra[i],
                Rule.Index => @as(Rule.Index, @enumFromInt(grammar.extra[i])),
                else => @compileError("bad field type"),
            };
            i += 1;
        }
        return .{
            .data = result,
            .end = i,
        };
    }

    pub fn nullTerminatedString(grammar: Grammar, pos: u32) [:0]const u8 {
        var end = pos;
        while (grammar.text[end] != 0)
            end += 1;
        return grammar.text[pos..end :0];
    }
};

pub const Token = struct {
    name_pos: u32,

    pub const Index = enum(u32) { _ };
};

pub const Node = struct {
    name_pos: u32,
    rule: Rule.Index,

    pub const Index = enum(u32) { _ };
};

pub const Rule = struct {
    tag: Tag,
    data: Data,

    pub const Index = enum(u32) { _ };

    const Tag = enum {
        label, // extra: Label
        node, // node
        token, // token
        seq, // extra: Bin
        alt, // extra: Bin
        opt, // rule
        rep, // rule
    };

    const Data = union {
        node: Node.Index,
        token: Token.Index,
        rule: Rule.Index,
        extra: u32,
    };

    const Label = struct {
        label_pos: u32,
        rule: Rule.Index,
    };

    const Bin = struct {
        lhs: Rule.Index,
        rhs: Rule.Index,
    };
};
