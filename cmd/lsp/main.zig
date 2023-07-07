const std = @import("std");
const lsp = @import("zig-lsp");
const Sema = @import("sema").Context;
const LineIndex = @import("sema").LineIndex;

const Connection = lsp.Connection(std.fs.File.Reader, std.fs.File.Writer, Context);

fn getDiagnostics(arena: *std.heap.ArenaAllocator, src: []const u8) error{OutOfMemory}![]lsp.types.Diagnostic {
    var ctx = try Sema.init(arena.allocator(), src);
    defer ctx.deinit();

    var diagnostics: std.ArrayListUnmanaged(lsp.types.Diagnostic) = .{};
    defer diagnostics.deinit(arena.allocator());

    if (ctx.compile()) |_| {
        const line_index = try LineIndex.make(ctx.allocator, src);
        defer line_index.deinit(ctx.allocator);
        for (ctx.diagnostics.items(.span), ctx.diagnostics.items(.message)) |span, message| {
            const start = line_index.translate(span.start.offset);
            const end = line_index.translate(span.end.offset);
            try diagnostics.append(arena.allocator(), .{
                .message = try arena.allocator().dupe(u8, message),
                .range = .{
                    .start = .{ .line = start.line, .character = start.col },
                    .end = .{ .line = end.line, .character = end.col },
                },
            });
        }
    } else |err| {
        std.debug.dumpStackTrace(@errorReturnTrace().?.*);
        try diagnostics.append(arena.allocator(), .{
            .message = @errorName(err),
            .range = .{
                .start = .{ .line = 1, .character = 1 },
                .end = .{ .line = 1, .character = 2 },
            },
        });
    }

    return diagnostics.toOwnedSlice(arena.allocator());
}

const Context = struct {
    pub fn initialize(conn: *Connection, id: lsp.types.RequestId, _: lsp.types.InitializeParams) !lsp.types.InitializeResult {
        _ = id;
        _ = conn;
        return .{
            .capabilities = .{
                .textDocumentSync = .{ .TextDocumentSyncKind = .Full },
            },
        };
    }

    pub fn @"textDocument/didOpen"(conn: *Connection, params: lsp.types.DidOpenTextDocumentParams) !void {
        var arena = std.heap.ArenaAllocator.init(conn.allocator);
        defer arena.deinit();

        const src = params.textDocument.text;
        var diagnostics = try getDiagnostics(&arena, src);
        defer arena.allocator().free(diagnostics);

        try conn.notify("textDocument/publishDiagnostics", .{
            .uri = params.textDocument.uri,
            .diagnostics = diagnostics,
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

        var diagnostics = try getDiagnostics(&arena, src);
        defer arena.allocator().free(diagnostics);

        try conn.notify("textDocument/publishDiagnostics", .{
            .uri = params.textDocument.uri,
            .diagnostics = diagnostics,
        });
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
