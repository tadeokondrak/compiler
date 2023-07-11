const std = @import("std");
const sema = @import("sema");

pub fn main() !void {
    const src =
        \\const num u32 = 1;
        \\const ptr *u64 = 0;
        \\struct Struct {
        \\    field1 u32;
        \\    field2 *u32;
        \\}
        \\struct Node {
        \\    next *Node;
        \\}
        \\struct Other {
        \\    field1 Struct;
        \\}
        \\fn infinite_loop() (ret u32) {
        \\    loop {}
        \\}
        \\fn add(a u32, b u32) (ret u32) {
        \\    return a + b;
        \\}
        \\fn fib(n u32) (ret u32) {
        \\    if n <= 1 {
        \\        return 1;
        \\    }
        \\    return add(fib(n - 1), fib(n - 2));
        \\}
    ;

    var gpa: std.heap.GeneralPurposeAllocator(.{ .stack_trace_frames = 32 }) = .{};
    defer _ = gpa.deinit();
    var ctx = try sema.Context.init(gpa.allocator(), src);
    defer ctx.deinit();
    //std.debug.print("syntax: {}\n", .{ctx.root});
    try ctx.compile();
    try ctx.dump(std.io.getStdErr().writer());
    if (try ctx.printDiagnostics(src, std.io.getStdErr().writer()))
        return;
}
