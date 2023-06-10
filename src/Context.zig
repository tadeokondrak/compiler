const std = @import("std");
const syntax = @import("syntax.zig");
const lex = @import("lex.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

const ast = syntax.ast;

const Context = @This();

allocator: std.mem.Allocator,
root: syntax.pure.Root,
decls: std.ArrayListUnmanaged(Decl) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
scopes: std.ArrayListUnmanaged(Scope) = .{},

const Decl = union(enum) {
    structure: Decl.Struct,
    function: Decl.Fn,
    constant: Decl.Const,

    const Index = enum(usize) { _ };

    const Key = union(enum) {
        structure: ast.Decl.Struct,
        function: ast.Decl.Fn,
        constant: ast.Decl.Const,
    };

    const Struct = struct {
        syntax: ast.Decl.Struct,
        name: []const u8,
    };

    const Fn = struct {
        syntax: ast.Decl.Fn,
        name: []const u8,
    };

    const Const = struct {
        syntax: ast.Decl.Const,
        name: []const u8,
    };

    fn matchesKey(decl: Decl, key: Decl.Key) bool {
        return switch (decl) {
            .structure => |structure| key == .structure and key.structure.tree == structure.syntax.tree,
            .function => |function| key == .function and key.function.tree == function.syntax.tree,
            .constant => |constant| key == .constant and key.constant.tree == constant.syntax.tree,
        };
    }
};

fn lookUpDecl(ctx: *Context, key: Decl.Key) error{OutOfMemory}!Decl.Index {
    for (ctx.decls.items, 0..) |decl, i| {
        if (decl.matchesKey(key))
            return @intToEnum(Decl.Index, i);
    }
    switch (key) {
        .structure => |structure_syntax| {
            const structure_ident = structure_syntax.ident(ctx.root).?;
            const name = ctx.root.tokenText(structure_ident);
            try ctx.decls.append(ctx.allocator, .{ .structure = .{
                .name = name,
                .syntax = structure_syntax,
            } });
            return @intToEnum(Decl.Index, ctx.decls.items.len - 1);
        },
        .function => |function_syntax| {
            const function_ident = function_syntax.ident(ctx.root).?;
            const name = ctx.root.tokenText(function_ident);
            try ctx.decls.append(ctx.allocator, .{ .function = .{
                .name = name,
                .syntax = function_syntax,
            } });
            return @intToEnum(Decl.Index, ctx.decls.items.len - 1);
        },
        .constant => |constant_syntax| {
            const constant_ident = constant_syntax.ident(ctx.root).?;
            const name = ctx.root.tokenText(constant_ident);
            try ctx.decls.append(ctx.allocator, .{ .constant = .{
                .name = name,
                .syntax = constant_syntax,
            } });
            return @intToEnum(Decl.Index, ctx.decls.items.len - 1);
        },
    }
}

const Type = union(enum) {
    invalid,
    integer: Type.Integer,
    structure: Decl.Index,
    function: Decl.Index,

    const Index = enum(usize) { _ };

    const Key = union(enum) {
        invalid,
        integer: struct { bits: u32 },
        structure: ast.Decl.Struct,
        function: ast.Decl.Fn,
    };

    const Integer = struct {
        signed: bool,
        bits: u32,
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

fn lookUpType(ctx: *Context, key: Type.Key) error{OutOfMemory}!Type.Index {
    for (ctx.types.items, 0..) |typ, i| {
        if (typ.matchesKey(key, ctx))
            return @intToEnum(Type.Index, i);
    }
    switch (key) {
        .invalid => {
            try ctx.types.append(ctx.allocator, .invalid);
            return @intToEnum(Type.Index, ctx.types.items.len - 1);
        },
        .integer => |integer_key| {
            try ctx.types.append(ctx.allocator, .{ .integer = .{ .bits = integer_key.bits } });
            return @intToEnum(Type.Index, ctx.types.items.len - 1);
        },
        .structure => |struct_syntax| {
            const struct_decl = ctx.lookUpDecl(.{ .structure = struct_syntax });
            try ctx.types.append(ctx.allocator, .{ .structure = struct_decl });
            return @intToEnum(Type.Index, ctx.decls.items.len - 1);
        },
        .function => |function_syntax| {
            const function_decl = ctx.lookUpDecl(.{ .function = function_syntax });
            try ctx.types.append(ctx.allocator, .{ .function = function_decl });
            return @intToEnum(Type.Index, ctx.decls.items.len - 1);
        },
    }
}

const Scope = struct {
    parent: Scope.Index,
    variant: Scope.Variant,

    const Index = enum(usize) {
        none = std.math.maxInt(usize),
        _,
    };

    const Key = union(enum) {
        root,
        decl: Context.Decl.Index,
    };

    const Variant = union(enum) {
        root,
        decl: Scope.Decl,
    };

    const Decl = struct {
        decl: Context.Decl.Index,
    };

    const LookupResult = union(enum) {
        not_found,
    };

    fn matchesKey(scope: Scope, key: Scope.Key) bool {
        return switch (key) {
            .root => scope.variant == .root,
            .decl => |decl| scope.variant == .decl and scope.variant.decl.decl == decl,
        };
    }

    //fn lookUpName(scope: Scope, context: Context) LookupResult {
    //    return .not_found;
    //}
};

fn lookUpScope(ctx: *Context, key: Scope.Key) error{OutOfMemory}!Scope.Index {
    for (ctx.scopes.items, 0..) |scope, i| {
        if (scope.matchesKey(key))
            return @intToEnum(Scope.Index, i);
    }
    switch (key) {
        .root => {
            try ctx.scopes.append(ctx.allocator, .{ .parent = .none, .variant = .root });
            return @intToEnum(Scope.Index, ctx.scopes.items.len - 1);
        },
        .decl => |decl| {
            const parent = try ctx.lookUpScope(.root);
            try ctx.scopes.append(ctx.allocator, .{ .parent = parent, .variant = .{ .decl = .{ .decl = decl } } });
            return @intToEnum(Scope.Index, ctx.scopes.items.len - 1);
        },
    }
}

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    var root = try parse.parseFile(allocator, src);
    return .{ .allocator = allocator, .root = root };
}

pub fn deinit(ctx: *Context) void {
    ctx.scopes.deinit(ctx.allocator);
    ctx.decls.deinit(ctx.allocator);
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn main(ctx: *Context) !void {
    const file = ast.File{ .tree = @intToEnum(syntax.pure.Tree.Index, 0) };
    var it = file.decls(ctx.root);
    var decls = std.StringHashMapUnmanaged(Decl.Index){};
    defer decls.deinit(ctx.allocator);
    while (it.next(ctx.root)) |decl_syntax| {
        switch (decl_syntax) {
            .function => |function| {
                const decl = try ctx.lookUpDecl(.{ .function = function });
                try decls.put(ctx.allocator, ctx.decls.items[@enumToInt(decl)].function.name, decl);
            },
            .structure => |structure| {
                const decl = try ctx.lookUpDecl(.{ .structure = structure });
                try decls.put(ctx.allocator, ctx.decls.items[@enumToInt(decl)].structure.name, decl);
            },
            .constant => |constant| {
                const decl = try ctx.lookUpDecl(.{ .constant = constant });
                try decls.put(ctx.allocator, ctx.decls.items[@enumToInt(decl)].constant.name, decl);
            },
        }
    }
    try ctx.analyzeDecl(decls.get("main").?);
}

fn analyzeDecl(ctx: *Context, decl: Decl.Index) !void {
    const data = ctx.decls.items[@enumToInt(decl)];
    switch (data) {
        .structure => |structure| {
            _ = structure;
        },
        .function => |function| {
            _ = try ctx.lookUpScope(.{ .decl = decl });
            var builder = ir.Builder{ .allocator = ctx.allocator };
            defer builder.func.deinit(ctx.allocator);
            const body = function.syntax.body(ctx.root) orelse return error.Syntax;
            builder.switchToBlock(try builder.addBlock());
            try ctx.genBlock(body, &builder);
            std.debug.print("{}\n", .{builder.func});
        },
        .constant => |constant| {
            _ = constant;
        },
    }
}

fn analyzeTypeExpr(ctx: *Context, type_expr: ast.TypeExpr) !Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = ident.ident(ctx.root) orelse return error.Syntax;
            const ident_text = ctx.root.tokenText(ident_token);
            if (std.mem.eql(u8, ident_text, "u32")) {
                return ctx.lookUpType(.{ .integer = .{ .signed = false, .bits = 32 } });
            }

            @panic("TODO");
        },
    }
}

fn genBlock(ctx: *Context, block: ast.Stmt.Block, builder: *ir.Builder) !void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const stmt = ast.Stmt.cast(ctx.root, child_tree) orelse return error.Syntax;
            switch (stmt) {
                .expr => |expr_stmt| {
                    const expr = expr_stmt.expr(ctx.root) orelse return error.Syntax;
                    _ = try ctx.genExpr(expr, builder);
                },
                .block => |nested_block| {
                    return ctx.genBlock(nested_block, builder);
                },
                .@"return" => |return_stmt| {
                    const expr = return_stmt.expr(ctx.root) orelse return error.Syntax;
                    const value = try ctx.genExpr(expr, builder);
                    try builder.buildRet(value.reg);
                },
            }
        }
    }
}

const Value = union(enum) {
    reg: ir.Reg,
};

fn genExpr(ctx: *Context, expr: ast.Expr, builder: *ir.Builder) !Value {
    switch (expr) {
        .unary => |unary| {
            _ = unary;
            return error.UnknownUnaryOperator;
        },
        .binary => |binary_expr| {
            if (binary_expr.plus(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .add);
            if (binary_expr.minus(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .sub);
            if (binary_expr.star(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .mul);
            if (binary_expr.slash(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .div);
            if (binary_expr.percent(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .rem);
            return error.UnknownBinaryOperator;
        },
        .literal => |literal| {
            if (literal.number(ctx.root)) |number| {
                const text = ctx.root.tokenText(number);
                const num = try std.fmt.parseInt(u64, text, 10);
                return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = num }) };
            }

            return error.UnknownLiteralKind;
        },
        .paren => |paren| {
            const inner = paren.expr(ctx.root) orelse return error.Syntax;
            return ctx.genExpr(inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse return error.Syntax;
            // TODO
            return ctx.genExpr(inner, builder);
        },
        .ident => |ident| {
            _ = ident;
            //ctx.lookUpScope(.{ .decl = decl });
            return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = 0 }) };
        },
    }
}

fn genBinExpr(ctx: *Context, expr: ast.Expr.Binary, builder: *ir.Builder, op: enum { add, sub, mul, div, rem }) !Value {
    const lhs = expr.lhs(ctx.root) orelse return error.Syntax;
    const rhs = expr.rhs(ctx.root) orelse return error.Syntax;
    const lhs_value = try ctx.genExpr(lhs, builder);
    const rhs_value = try ctx.genExpr(rhs, builder);
    return switch (op) {
        .add => .{ .reg = try builder.buildAdd(lhs_value.reg, rhs_value.reg) },
        .sub => unreachable, //.{ .reg = try builder.buildSub(lhs_value.reg, rhs_value.reg) },
        .mul => unreachable, //.{ .reg = try builder.buildMul(lhs_value.reg, rhs_value.reg) },
        .div => unreachable, //.{ .reg = try builder.buildDiv(lhs_value.reg, rhs_value.reg) },
        .rem => unreachable, //.{ .reg = try builder.buildRem(lhs_value.reg, rhs_value.reg) },
    };
}
