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
decls: std.ArrayListUnmanaged(Decl) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
structs: std.ArrayListUnmanaged(Struct) = .{},

const Decl = union(enum) {
    structure: Decl.Struct,
    function: Decl.Fn,

    const Index = struct { index: usize };

    const Struct = struct {
        syntax: ast.Decl.Struct,
        name: []const u8,
    };

    const Fn = struct {
        syntax: ast.Decl.Fn,
        name: []const u8,
    };
};

const Type = union(enum) {
    invalid,
    integer: struct { bits: u32 },
    structure: Decl.Index,
    function: Decl.Index,

    const Index = struct { index: usize };

    const Key = union(enum) {
        invalid,
        integer: struct { bits: u32 },
        structure: ast.Decl.Struct,
        function: ast.Decl.Fn,
    };

    fn matchesKey(typ: Type, key: Type.Key, ctx: *Context) bool {
        return switch (typ) {
            .invalid => key == .invalid,
            .integer => |integer_type| key == .integer and key.integer.bits == integer_type.bits,
            .structure => |structure| key == .structure and key.structure.tree.index == ctx.decls.items[structure.index].structure.syntax.tree.index,
            .function => |function| key == .function and key.function.tree.index == ctx.decls.items[function.index].function.syntax.tree.index,
        };
    }
};

const Value = union(enum) {
    reg: ir.Reg,
};

const Struct = struct {
    const Index = struct { index: usize };

    decl: ast.Decl.Struct,
    name: []const u8,
    fields: std.ArrayListUnmanaged(Field) = .{},

    const Field = struct {
        name: []const u8,
        type: Type.Index,
    };
};

fn getTypeByKey(ctx: *Context, key: Type.Key) error{ OutOfMemory, Syntax }!Type.Index {
    for (ctx.types.items, 0..) |typ, i| {
        if (typ.matchesKey(key, ctx))
            return Type.Index{ .index = i };
    }
    switch (key) {
        .invalid => {
            try ctx.types.append(ctx.allocator, .invalid);
            return Type.Index{ .index = ctx.types.items.len - 1 };
        },
        .integer => |integer_key| {
            try ctx.types.append(ctx.allocator, .{ .integer = .{ .bits = integer_key.bits } });
            return Type.Index{ .index = ctx.types.items.len - 1 };
        },
        .structure => |struct_syntax| {
            const struct_ident = struct_syntax.ident(ctx.root) orelse return error.Syntax;
            const struct_name = ctx.root.tokenText(struct_ident);
            try ctx.decls.append(ctx.allocator, .{ .structure = Decl.Struct{ .syntax = struct_syntax, .name = struct_name } });
            try ctx.types.append(ctx.allocator, .{ .structure = Decl.Index{ .index = ctx.decls.items.len - 1 } });
            return Type.Index{ .index = ctx.decls.items.len - 1 };
        },
        .function => |function_syntax| {
            const function_ident = function_syntax.ident(ctx.root) orelse return error.Syntax;
            const function_name = ctx.root.tokenText(function_ident);
            try ctx.decls.append(ctx.allocator, .{ .function = Decl.Fn{ .syntax = function_syntax, .name = function_name } });
            try ctx.types.append(ctx.allocator, .{ .function = Decl.Index{ .index = ctx.decls.items.len - 1 } });
            return Type.Index{ .index = ctx.decls.items.len - 1 };
        },
    }
}

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    var root = try parse.parseFile(allocator, src);
    const file = ast.File{ .tree = syntax.Tree.Index{ .index = 0 } };
    return .{
        .allocator = allocator,
        .root = root,
        .file = file,
    };
}

pub fn deinit(ctx: *Context) void {
    ctx.decls.deinit(ctx.allocator);
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn main(ctx: *Context) !void {
    var it = ctx.file.decls(ctx.root);
    var map = std.StringHashMapUnmanaged(Type.Index){};
    defer map.deinit(ctx.allocator);
    while (it.next(ctx.root)) |decl| {
        switch (decl) {
            .function => |function| {
                const typ = try ctx.getTypeByKey(.{ .function = function });
                try map.put(ctx.allocator, ctx.root.tokenText(function.ident(ctx.root).?), typ);
            },
            .structure => |structure| {
                const typ = try ctx.getTypeByKey(.{ .structure = structure });
                try map.put(ctx.allocator, ctx.root.tokenText(structure.ident(ctx.root).?), typ);
            },
        }
    }
}

//fn analyzeFunction(ctx: *Context, function: ast.Decl.Fn) !void {
//    var builder = ir.Builder{ .allocator = ctx.allocator };
//    defer builder.func.deinit(ctx.allocator);
//    const name = function.ident(ctx.root) orelse return error.Syntax;
//    const name_text = ctx.root.tokenText(name);
//    const block = function.body(ctx.root) orelse return error.Syntax;
//    builder.switchToBlock(try builder.addBlock());
//    try ctx.genBlock(block, &builder);
//    std.debug.print("{s}: {}\n", .{ name_text, builder.func });
//}
//
//fn analyzeTypeExpr(ctx: *Context, type_expr: ast.TypeExpr) !Type.Index {
//    switch (type_expr) {
//        .ident => |ident| {
//            const ident_token = ident.ident(ctx.root) orelse return error.Syntax;
//            const ident_text = ctx.root.tokenText(ident_token);
//            if (std.mem.eql(u8, ident_text, "u32")) {
//                return ctx.getTypeByKey(.{ .integer = .{ .bits = 32 } });
//            }
//
//            @panic("TODO");
//        },
//    }
//}
//
//fn genBlock(ctx: *Context, block: ast.Stmt.Block, builder: *ir.Builder) !void {
//    for (ctx.root.treeChildren(block.tree)) |child| {
//        if (child.asTree()) |child_tree| {
//            const stmt = ast.Stmt.cast(ctx.root, child_tree) orelse return error.ExpectedStatement;
//            switch (stmt) {
//                .expr => |expr_stmt| {
//                    const expr = expr_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
//                    _ = try ctx.genExpr(expr, builder);
//                },
//                .block => |nested_block| {
//                    return ctx.genBlock(nested_block, builder);
//                },
//                .@"return" => |return_stmt| {
//                    const expr = return_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
//                    const value = try ctx.genExpr(expr, builder);
//                    try builder.buildRet(value.reg);
//                },
//            }
//        }
//    }
//}
//
//fn genExpr(ctx: *Context, expr: ast.Expr, builder: *ir.Builder) !Value {
//    switch (expr) {
//        .unary => |unary| {
//            _ = unary;
//            return error.UnknownUnaryOperator;
//        },
//        .binary => |binary_expr| {
//            if (binary_expr.plus(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .add);
//            if (binary_expr.minus(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .sub);
//            if (binary_expr.star(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .mul);
//            if (binary_expr.slash(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .div);
//            if (binary_expr.percent(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .rem);
//            return error.UnknownBinaryOperator;
//        },
//        .literal => |literal| {
//            if (literal.number(ctx.root)) |number| {
//                const text = ctx.root.tokenText(number);
//                const num = try std.fmt.parseInt(u64, text, 10);
//                return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = num }) };
//            }
//
//            return error.UnknownLiteralKind;
//        },
//        .paren => |paren| {
//            const inner = paren.expr(ctx.root) orelse return error.ExpectedExpression;
//            return ctx.genExpr(inner, builder);
//        },
//        .call => |call| {
//            const inner = call.expr(ctx.root) orelse return error.ExpectedExpression;
//            // TODO
//            return ctx.genExpr(inner, builder);
//        },
//        .ident => |ident| {
//            _ = ident;
//            return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = 0 }) };
//        },
//    }
//}
//
//fn genBinExpr(ctx: *Context, expr: ast.Expr.Binary, builder: *ir.Builder, op: enum { add, sub, mul, div, rem }) !Value {
//    const lhs = expr.lhs(ctx.root) orelse return error.ExpectedExpression;
//    const rhs = expr.rhs(ctx.root) orelse return error.ExpectedExpression;
//    const lhs_value = try ctx.genExpr(lhs, builder);
//    const rhs_value = try ctx.genExpr(rhs, builder);
//    return switch (op) {
//        .add => .{ .reg = try builder.buildAdd(lhs_value.reg, rhs_value.reg) },
//        .sub => unreachable, //.{ .reg = try builder.buildSub(lhs_value.reg, rhs_value.reg) },
//        .mul => unreachable, //.{ .reg = try builder.buildMul(lhs_value.reg, rhs_value.reg) },
//        .div => unreachable, //.{ .reg = try builder.buildDiv(lhs_value.reg, rhs_value.reg) },
//        .rem => unreachable, //.{ .reg = try builder.buildRem(lhs_value.reg, rhs_value.reg) },
//    };
//}
