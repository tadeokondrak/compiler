const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const ast = @import("ast.zig");
const parse = @import("parse.zig");

const source =
    \\fn main() {
    \\    return 1 + 1 + 2;
    \\}
;

pub fn main() !void {
    std.debug.print("source: '{s}'\n", .{source});
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    var root = try parse.parseFile(gpa.allocator(), source);
    defer root.deinit(gpa.allocator());
    const file = ast.File{ .tree = @intToEnum(syntax.Tree, 0) };
    std.debug.print("tree: '{}'\n", .{root});
    const result = runMain(root, file);
    std.debug.print("result: {}\n", .{try result});
}

fn runMain(root: syntax.Root, file: ast.File) !u8 {
    const function = file.function(root) orelse return error.MissingFunction;
    const body = function.body(root) orelse return error.MissingFunctionBody;
    return runBlock(root, body);
}

fn runBlock(root: syntax.Root, block: ast.StmtBlock) !u8 {
    for (root.treeChildren(block.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const stmt = ast.Stmt.cast(root, child_tree) orelse return error.ExpectedStatement;
            switch (stmt) {
                .expr => |expr_stmt| {
                    const expr = expr_stmt.expr(root) orelse return error.ExpectedExpression;
                    switch (try evalExpr(root, expr)) {
                        .value => {},
                        .returned => |val| return val,
                    }
                },
                .block => |nested_block| {
                    return runBlock(root, nested_block);
                },
            }
        }
    }

    return error.DidNotReturn;
}

const ExprEvalResult = union(enum) {
    value: u8,
    returned: u8,
};

fn evalExpr(root: syntax.Root, expr: ast.Expr) !ExprEvalResult {
    switch (expr) {
        .unary => |unary| {
            if (unary.kw_return(root)) |_| {
                const returned = unary.expr(root) orelse return error.ExpectedExpression;
                return .{ .returned = (try evalExpr(root, returned)).value };
            }

            return error.UnknownUnop;
        },
        .binary => |binary| {
            if (binary.plus(root)) |_| {
                const lhs = binary.lhs(root) orelse return error.ExpectedExpression;
                const rhs = binary.rhs(root) orelse return error.ExpectedExpression;
                const lhs_value = (try evalExpr(root, lhs)).value;
                const rhs_value = (try evalExpr(root, rhs)).value;
                return .{ .value = lhs_value + rhs_value };
            }

            return error.UnknownBinop;
        },
        .literal => |literal| {
            const text = root.tokenText(literal.number(root).?);
            return .{ .value = try std.fmt.parseInt(u8, text, 10) };
        },
        .paren => |paren| {
            const inner = paren.expr(root) orelse return error.ExpectedExpression;
            return evalExpr(root, inner);
        },
    }
}

comptime {
    _ = syntax;
    _ = ast;
    _ = lex;
    _ = parse;
}
