const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const ast = @import("ast.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

const Context = @This();

allocator: std.mem.Allocator,
root: syntax.Root,
file: ast.File,
types: std.ArrayListUnmanaged(Type) = .{},
structs: std.ArrayListUnmanaged(Struct) = .{},

const Type = union(enum) {
    const Index = struct { index: usize };

    invalid,
    untyped_number,
    integer: struct { bits: u32 },
    structure: Struct,
};

const Value = union(enum) {
    reg: ir.Reg,
    untyped_number: std.math.big.int.Const,
};

const Struct = struct {
    const Index = struct { index: usize };

    name: []const u8,
    fields: std.ArrayListUnmanaged(Field) = .{},

    const Field = struct {
        name: []const u8,
        type: Type.Index,
    };
};

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    var root = try parse.parseFile(allocator, src);
    const file = ast.File{ .tree = syntax.Tree{ .index = 0 } };
    return .{
        .allocator = allocator,
        .root = root,
        .file = file,
    };
}

pub fn deinit(ctx: *Context) void {
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn analyzeDecls(ctx: *Context) !void {
    var it = ctx.file.decls(ctx.root);
    while (it.next(ctx.root)) |decl| {
        switch (decl) {
            .function => |function| try ctx.analyzeFunction(function),
            .constant => {},
            .structure => |structure| try ctx.analyzeStruct(structure),
        }
    }
}

fn analyzeFunction(ctx: *Context, function: ast.Decl.Fn) !void {
    var builder = ir.Builder{ .allocator = ctx.allocator };
    defer builder.func.deinit(ctx.allocator);
    const name = function.ident(ctx.root) orelse return error.MissingFunctionName;
    const name_text = ctx.root.tokenText(name);
    const block = function.body(ctx.root) orelse return error.MissingFunctionBody;
    builder.switchToBlock(try builder.addBlock());
    try ctx.genBlock(block, &builder);
    std.debug.print("{s}: {}\n", .{ name_text, builder.func });
}

fn analyzeStruct(ctx: *Context, structure: ast.Decl.Struct) !void {
    for (ctx.root.treeChildren(structure.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const field = ast.Decl.Struct.Field.cast(ctx.root, child_tree) orelse return error.ExpectedStructField;
            const name = field.ident(ctx.root) orelse return error.MissingStructFieldName;
            const name_text = ctx.root.tokenText(name);
            std.debug.print("field: {s}\n", .{name_text});
        }
    }
}

fn genBlock(ctx: *Context, block: ast.Stmt.Block, builder: *ir.Builder) !void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const stmt = ast.Stmt.cast(ctx.root, child_tree) orelse return error.ExpectedStatement;
            switch (stmt) {
                .expr => |expr_stmt| {
                    const expr = expr_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
                    _ = try ctx.genExpr(expr, builder);
                },
                .block => |nested_block| {
                    return ctx.genBlock(nested_block, builder);
                },
                .@"return" => |return_stmt| {
                    const expr = return_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
                    const value = try ctx.genExpr(expr, builder) orelse return error.ExpectedReturnValue;
                    try builder.buildRet(value);
                },
            }
        }
    }
}

fn genExpr(ctx: *Context, expr: ast.Expr, builder: *ir.Builder) !?ir.Reg {
    switch (expr) {
        .unary => |unary| {
            _ = unary;
            return error.UnknownUnop;
        },
        .binary => |binary| {
            if (binary.plus(ctx.root)) |_| {
                const lhs = binary.lhs(ctx.root) orelse return error.ExpectedExpression;
                const rhs = binary.rhs(ctx.root) orelse return error.ExpectedExpression;
                const lhs_value = try ctx.genExpr(lhs, builder) orelse return error.ExpectedValue;
                const rhs_value = try ctx.genExpr(rhs, builder) orelse return error.ExpectedValue;

                return try builder.buildAdd(lhs_value, rhs_value);
            }

            return error.UnknownBinop;
        },
        .literal => |literal| {
            if (literal.number(ctx.root)) |number| {
                const text = ctx.root.tokenText(number);
                const num = try std.fmt.parseInt(u64, text, 10);
                return try builder.buildConstant(.i64, ir.Value{ .bits = num });
            }

            return error.UnknownLiteral;
        },
        .paren => |paren| {
            const inner = paren.expr(ctx.root) orelse return error.ExpectedExpression;
            return ctx.genExpr(inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse return error.ExpectedExpression;
            // TODO
            return ctx.genExpr(inner, builder);
        },
        .ident => |ident| {
            _ = ident;
            return try builder.buildConstant(.i64, ir.Value{ .bits = 0 });
        },
    }
}
