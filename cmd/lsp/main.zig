const std = @import("std");
const lsp = @import("zig-lsp");
const syntax = @import("syntax");
const parse = @import("parse");
const sema = @import("sema");

const LineIndex = sema.LineIndex;

const Connection = lsp.Connection(std.fs.File.Reader, std.fs.File.Writer, Context);

const Document = struct {
    arena: std.heap.ArenaAllocator,
    sema: sema.Context,
    syntax: syntax.Context,
    line_index: LineIndex,

    fn init(doc: *Document, allocator: std.mem.Allocator, src: []const u8) !void {
        doc.arena = std.heap.ArenaAllocator.init(allocator);
        const parsed = try parse.parseFile(doc.arena.allocator(), src);
        doc.sema = try sema.Context.init(doc.arena.allocator(), src);
        doc.syntax = .{
            .arena = doc.arena.allocator(),
            .root = parsed.root,
        };
        doc.line_index = try LineIndex.make(doc.arena.allocator(), src);
        try doc.sema.compile();
    }

    fn updateContent(doc: *Document, src: []const u8) !void {
        doc.sema.deinit();
        doc.sema = try sema.Context.init(doc.arena.allocator(), src);
        try doc.sema.compile();
        doc.syntax.root.deinit(doc.arena.allocator());
        doc.syntax.root = (try parse.parseFile(doc.arena.allocator(), src)).root;
        doc.line_index.deinit(doc.arena.allocator());
        doc.line_index = try LineIndex.make(doc.arena.allocator(), src);
    }

    fn translateSpan(doc: *Document, span: syntax.pure.Span) lsp.types.Range {
        const start = doc.line_index.translate(span.start.offset);
        const end = doc.line_index.translate(span.end.offset);
        return .{
            .start = .{ .line = start.line, .character = start.col },
            .end = .{ .line = end.line, .character = end.col },
        };
    }

    fn translatePosition(doc: *Document, position: lsp.types.Position) syntax.pure.Pos {
        const line_start = if (position.line == 0) 0 else doc.line_index.newlines[position.line - 1];
        return .{ .offset = line_start + position.character };
    }
};

const Context = struct {
    docs: std.StringArrayHashMapUnmanaged(Document) = .{},

    pub fn initialize(conn: *Connection, id: lsp.types.RequestId, _: lsp.types.InitializeParams) !lsp.types.InitializeResult {
        _ = id;
        _ = conn;
        return .{
            .capabilities = .{
                .textDocumentSync = .{ .TextDocumentSyncKind = .Full },
                .hoverProvider = .{ .bool = true },
                .selectionRangeProvider = .{ .bool = true },
            },
        };
    }

    pub fn @"textDocument/didOpen"(conn: *Connection, params: lsp.types.DidOpenTextDocumentParams) !void {
        var arena = std.heap.ArenaAllocator.init(conn.allocator);
        defer arena.deinit();

        const gop = try conn.context.docs.getOrPut(conn.allocator, params.textDocument.uri);
        if (!gop.found_existing) {
            gop.key_ptr.* = try conn.allocator.dupe(u8, params.textDocument.uri);
            try gop.value_ptr.init(conn.allocator, params.textDocument.text);
        } else {
            try gop.value_ptr.updateContent(params.textDocument.text);
        }

        const doc = gop.value_ptr;

        var diagnostics: std.ArrayListUnmanaged(lsp.types.Diagnostic) = .{};
        defer diagnostics.deinit(arena.allocator());
        for (doc.sema.diagnostics.items(.span), doc.sema.diagnostics.items(.message)) |span, message| {
            try diagnostics.append(arena.allocator(), .{
                .message = message,
                .range = doc.translateSpan(span),
            });
        }

        try conn.notify("textDocument/publishDiagnostics", .{
            .uri = params.textDocument.uri,
            .diagnostics = diagnostics.items,
        });
    }

    pub fn @"textDocument/didChange"(conn: *Connection, params: lsp.types.DidChangeTextDocumentParams) !void {
        var arena = std.heap.ArenaAllocator.init(conn.allocator);
        defer arena.deinit();

        const src: []const u8 = blk: {
            for (params.contentChanges) |change| {
                switch (change) {
                    .literal_0 => |x| {
                        break :blk x.text;
                    },
                    .literal_1 => |x| {
                        break :blk x.text;
                    },
                }
            }
            return;
        };

        const doc = conn.context.docs.getPtr(params.textDocument.uri) orelse
            return error.NoTextDocument;
        try doc.updateContent(src);

        var diagnostics: std.ArrayListUnmanaged(lsp.types.Diagnostic) = .{};
        defer diagnostics.deinit(arena.allocator());
        for (doc.sema.diagnostics.items(.span), doc.sema.diagnostics.items(.message)) |span, message| {
            try diagnostics.append(arena.allocator(), .{
                .message = message,
                .range = doc.translateSpan(span),
            });
        }

        try conn.notify("textDocument/publishDiagnostics", .{
            .uri = params.textDocument.uri,
            .diagnostics = diagnostics.items,
        });
    }

    pub fn @"textDocument/hover"(conn: *Connection, _: lsp.types.RequestId, params: lsp.types.HoverParams) !lsp.types.Hover {
        var arena = std.heap.ArenaAllocator.init(conn.allocator);
        defer arena.deinit();

        const doc = conn.context.docs.getPtr(params.textDocument.uri) orelse return error.TODO;
        const pos = doc.translatePosition(params.position);
        const decl_syntax = doc.sema.findDecl(.{ .offset = pos.offset }) orelse return error.TODO;

        const text = switch (decl_syntax) {
            .function => |function| blk: {
                const ty = try doc.sema.lookUpType(.{ .function = function });
                break :blk try std.fmt.allocPrint(conn.allocator, "```\n{code}\n```", .{doc.sema.fmtType(ty)});
            },
            .structure => |structure| blk: {
                const ty = try doc.sema.lookUpType(.{ .structure = structure });
                break :blk try std.fmt.allocPrint(conn.allocator, "```\n{#}\n```", .{doc.sema.fmtType(ty)});
            },
            .constant => blk: {
                break :blk try std.fmt.allocPrint(conn.allocator, "constant", .{});
            },
        };

        return .{
            .contents = .{
                .MarkupContent = .{
                    .kind = .markdown,
                    .value = text,
                },
            },
            .range = doc.translateSpan(doc.sema.root.treeSpan(decl_syntax.tree())),
        };
    }

    pub fn @"textDocument/selectionRange"(conn: *Connection, _: lsp.types.RequestId, params: lsp.types.SelectionRangeParams) !?[]lsp.types.SelectionRange {
        var arena = std.heap.ArenaAllocator.init(conn.allocator);
        defer arena.deinit();

        const doc = conn.context.docs.getPtr(params.textDocument.uri) orelse return error.TODO;

        // TODO: don't leak once I can figure out how to use this LSP abstraction
        const ranges = try conn.allocator.alloc(lsp.types.SelectionRange, params.positions.len);

        for (params.positions, 0..) |pos, i| {
            const root: *syntax.Tree = try doc.syntax.createTree(@enumFromInt(0));
            const token = try root.findToken(doc.translatePosition(pos)) orelse return null;
            ranges[i] = .{
                .range = doc.translateSpan(token.span()),
            };
            var parent: ?*const syntax.Tree = token.parent;
            var largest_range = &ranges[i];
            while (parent) |parent_tree| : (parent = parent_tree.parent) {
                const range = try conn.allocator.create(lsp.types.SelectionRange);
                range.* = .{
                    .range = doc.translateSpan(parent_tree.span()),
                };
                largest_range.parent = range;
                largest_range = range;
            }
        }

        return ranges;
    }
};

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{ .stack_trace_frames = 32 }) = .{};
    defer _ = gpa.deinit();
    var ctx = Context{};
    var conn = Connection.init(gpa.allocator(), std.io.getStdIn().reader(), std.io.getStdOut().writer(), &ctx);
    while (true) {
        var arena = std.heap.ArenaAllocator.init(gpa.allocator());
        defer arena.deinit();
        try conn.accept(arena.allocator());
    }
}
