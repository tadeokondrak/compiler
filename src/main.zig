const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const ast = @import("ast.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

comptime {
    _ = syntax;
    _ = lex;
    _ = ast;
    _ = parse;
    _ = ir;
}

const Type = enum {
    invalid,
    never,
    unit,
    i32,
    string,
};

const source =
    \\struct Struct {
    \\    field1: u32;
    \\    field2: u32;
    \\}
    \\fn main(x: u32) {
    \\    return 1 + 1 + 2 + f();
    \\}
;

pub fn main() !void {
    std.debug.print("source: '{s}'\n", .{source});
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    var root = try parse.parseFile(gpa.allocator(), source);
    defer root.deinit(gpa.allocator());
    const file = ast.File{ .tree = syntax.Tree.Index{ .index = 0 } };
    std.debug.print("tree: '{}'\n", .{root});
    var it = file.decls(root);
    while (it.next(root)) |decl| {
        switch (decl) {
            .function => |function| {
                var builder = ir.Builder{ .allocator = gpa.allocator() };
                defer builder.func.deinit(gpa.allocator());
                const name = function.ident(root) orelse return error.MissingFunctionName;
                const name_text = root.tokenText(name);
                const block = function.body(root) orelse return error.MissingFunctionBody;
                builder.switchToBlock(try builder.addBlock());
                try genBlock(root, block, &builder);
                std.debug.print("{s}: {}\n", .{ name_text, builder.func });
            },
            .constant => {},
        }
    }
}

fn genBlock(root: syntax.Root, block: ast.Stmt.Block, builder: *ir.Builder) !void {
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
                .@"return" => |return_stmt| {
                    const expr = return_stmt.expr(root) orelse return error.ExpectedExpression;
                    const value = try genExpr(root, expr, builder) orelse return error.ExpectedReturnValue;
                    try builder.buildRet(value);
                },
            }
        }
    }
}

fn genExpr(root: syntax.Root, expr: ast.Expr, builder: *ir.Builder) !?ir.Reg {
    const typeof = try typeOfExpr(root, expr);
    std.debug.print("typeof: {}\n", .{typeof});

    switch (expr) {
        .unary => |unary| {
            _ = unary;
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
        .call => |call| {
            const inner = call.expr(root) orelse return error.ExpectedExpression;
            // TODO
            return genExpr(root, inner, builder);
        },
        .ident => |ident| {
            _ = ident;
            return try builder.buildConstant(.i64, ir.Value{ .bits = 0 });
        },
    }
}

fn typeOfExpr(root: syntax.Root, expr: ast.Expr) !Type {
    switch (expr) {
        .unary => |unary| {
            _ = unary;
            return error.UnknownUnop;
        },
        .binary => |binary| {
            if (binary.plus(root)) |_| {
                const lhs = binary.lhs(root) orelse return error.ExpectedExpression;
                const rhs = binary.rhs(root) orelse return error.ExpectedExpression;
                const lhs_type = try typeOfExpr(root, lhs);
                const rhs_type = try typeOfExpr(root, rhs);
                if (lhs_type == Type.i32 and rhs_type == Type.i32) {
                    return Type.i32;
                }

                return error.TypeError;
            }

            return error.UnknownBinop;
        },
        .literal => |literal| {
            if (literal.number(root)) |number| {
                _ = number;
                return Type.i32;
            }

            if (literal.string(root)) |string| {
                _ = string;
                return Type.string;
            }

            return error.UnknownLiteral;
        },
        .paren => |paren| {
            const inner = paren.expr(root) orelse return error.ExpectedExpression;
            return typeOfExpr(root, inner);
        },
        .call => |call| {
            const f = call.expr(root) orelse return error.ExpectedExpression;
            // TODO
            return typeOfExpr(root, f);
        },
        .ident => {
            // TODO
            return Type.i32;
        },
    }
}
