pub const ast = @import("syntax/ast.zig");
pub const pure = @import("syntax/pure.zig");

comptime {
    _ = ast;
    _ = pure;
}
