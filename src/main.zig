const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const ast = @import("ast.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

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

    var builder = ir.Builder{ .allocator = gpa.allocator() };
    const result = try genFunc(root, file, &builder);
    _ = result;
    std.debug.print("result: {}\n", .{builder.func});
}

fn genFunc(root: syntax.Root, file: ast.File, builder: *ir.Builder) !void {
    const function = file.function(root) orelse return error.MissingFunction;
    const body = function.body(root) orelse return error.MissingFunctionBody;
    builder.switchToBlock(try builder.addBlock());
    return genBlock(root, body, builder);
}

fn genBlock(root: syntax.Root, block: ast.StmtBlock, builder: *ir.Builder) !void {
    for (root.treeChildren(block.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const stmt = ast.Stmt.cast(root, child_tree) orelse return error.ExpectedStatement;
            switch (stmt) {
                .expr => |expr_stmt| {
                    const expr = expr_stmt.expr(root) orelse return error.ExpectedExpression;
                    _ = try genExpr(root, expr, builder);
                },
                .block => |nested_block| {
                    return genBlock(root, nested_block, builder);
                },
            }
        }
    }
}

fn genExpr(root: syntax.Root, expr: ast.Expr, builder: *ir.Builder) !?ir.Reg {
    switch (expr) {
        .unary => |unary| {
            if (unary.kw_return(root)) |_| {
                const returned = unary.expr(root) orelse return error.ExpectedExpression;
                try builder.buildRet(try genExpr(root, returned, builder) orelse return error.ExpectedReturnValue);
                return null;
            }

            return error.UnknownUnop;
        },
        .binary => |binary| {
            if (binary.plus(root)) |_| {
                const lhs = binary.lhs(root) orelse return error.ExpectedExpression;
                const rhs = binary.rhs(root) orelse return error.ExpectedExpression;
                const lhs_value = try genExpr(root, lhs, builder) orelse return error.ExpectedValue;
                const rhs_value = try genExpr(root, rhs, builder) orelse return error.ExpectedValue;

                return try builder.buildAdd(lhs_value, rhs_value);
            }

            return error.UnknownBinop;
        },
        .literal => |literal| {
            if (literal.number(root)) |number| {
                const text = root.tokenText(number);
                const num = try std.fmt.parseInt(u64, text, 10);
                return try builder.buildConstant(.i64, ir.Value{ .bits = num });
            }

            return error.UnknownLiteral;
        },
        .paren => |paren| {
            const inner = paren.expr(root) orelse return error.ExpectedExpression;
            return genExpr(root, inner, builder);
        },
    }
}

comptime {
    _ = syntax;
    _ = ast;
    _ = lex;
    _ = parse;
}
