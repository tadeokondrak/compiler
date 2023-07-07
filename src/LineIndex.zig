const LineIndex = @This();

const std = @import("std");

newlines: []const u32,

pub fn make(allocator: std.mem.Allocator, src: []const u8) !LineIndex {
    var newlines: std.ArrayListUnmanaged(u32) = .{};
    for (src, 0..) |c, i| if (c == '\n') try newlines.append(allocator, @intCast(i));
    return .{ .newlines = try newlines.toOwnedSlice(allocator) };
}

pub fn deinit(index: LineIndex, allocator: std.mem.Allocator) void {
    allocator.free(index.newlines);
}

pub fn translate(index: LineIndex, offset: u32) struct { line: u32, col: u32 } {
    var line: u32 = 0;
    var col: u32 = offset;
    for (index.newlines) |i| {
        if (i >= offset) break;
        line += 1;
        col = offset - i;
    }
    return .{ .line = line, .col = col - 1 };
}
