const std = @import("std");
const syntax = @import("syntax.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

const ast = syntax.ast;

const Context = @This();

allocator: std.mem.Allocator,
root: syntax.pure.Root,
ast: ast.File,
decls: std.ArrayListUnmanaged(Decl) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
decls_by_name: std.StringHashMapUnmanaged(Decl.Index) = .{},

const Decl = union(enum) {
    structure: Decl.Struct,
    function: Decl.Fn,
    constant: Decl.Const,

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const Key = union(enum) {
        structure: ast.Decl.Struct,
        function: ast.Decl.Fn,
        constant: ast.Decl.Const,
    };

    const Struct = struct {
        syntax: ast.Decl.Struct,
        name: []const u8,
        ty: Type.Index = .invalid,
        fields: std.StringArrayHashMapUnmanaged(Type.Index) = .{},
    };

    const Fn = struct {
        syntax: ast.Decl.Fn,
        name: []const u8,
    };

    const Const = struct {
        syntax: ast.Decl.Const,
        name: []const u8,
        ty: Type.Index = .invalid,
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

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const Key = union(enum) {
        invalid,
        integer: struct { signed: bool, bits: u32 },
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
            .structure => |structure| key == .structure and key.structure.tree == ctx.decls.items[@enumToInt(structure)].structure.syntax.tree,
            .function => |function| key == .function and key.function.tree == ctx.decls.items[@enumToInt(function)].function.syntax.tree,
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
            try ctx.types.append(ctx.allocator, .{ .integer = .{ .signed = integer_key.signed, .bits = integer_key.bits } });
            return @intToEnum(Type.Index, ctx.types.items.len - 1);
        },
        .structure => |struct_syntax| {
            const struct_decl = try ctx.lookUpDecl(.{ .structure = struct_syntax });
            try ctx.types.append(ctx.allocator, .{ .structure = struct_decl });
            const ty = @intToEnum(Type.Index, ctx.decls.items.len - 1);
            std.debug.assert(ctx.decls.items[@enumToInt(struct_decl)].structure.ty == .invalid);
            ctx.decls.items[@enumToInt(struct_decl)].structure.ty = ty;
            return ty;
        },
        .function => |function_syntax| {
            const function_decl = try ctx.lookUpDecl(.{ .function = function_syntax });
            try ctx.types.append(ctx.allocator, .{ .function = function_decl });
            return @intToEnum(Type.Index, ctx.decls.items.len - 1);
        },
    }
}

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    const parsed = try parse.parseFile(allocator, src);
    return .{
        .allocator = allocator,
        .root = parsed.root,
        .ast = parsed.ast,
    };
}

pub fn deinit(ctx: *Context) void {
    for (ctx.decls.items) |*decl| {
        switch (decl.*) {
            .structure => |*structure| {
                structure.fields.deinit(ctx.allocator);
            },
            else => {},
        }
    }
    ctx.decls_by_name.deinit(ctx.allocator);
    ctx.decls.deinit(ctx.allocator);
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn populateDeclMap(ctx: *Context) !void {
    std.debug.assert(ctx.decls_by_name.size == 0);
    var it = ctx.ast.decls(ctx.root);
    while (it.next(ctx.root)) |decl_syntax| {
        switch (decl_syntax) {
            .function => |function| {
                const decl = try ctx.lookUpDecl(.{ .function = function });
                const name = ctx.decls.items[@enumToInt(decl)].function.name;
                try ctx.decls_by_name.put(ctx.allocator, name, decl);
            },
            .structure => |structure| {
                const decl = try ctx.lookUpDecl(.{ .structure = structure });
                const name = ctx.decls.items[@enumToInt(decl)].structure.name;
                try ctx.decls_by_name.put(ctx.allocator, name, decl);
            },
            .constant => |constant| {
                const decl = try ctx.lookUpDecl(.{ .constant = constant });
                const name = ctx.decls.items[@enumToInt(decl)].constant.name;
                try ctx.decls_by_name.put(ctx.allocator, name, decl);
            },
        }
    }
}

pub fn analyzeDecls(ctx: *Context) !void {
    for (ctx.decls.items, 0..) |_, i| {
        try ctx.analyzeDecl(@intToEnum(Decl.Index, i));
    }
}

fn analyzeDecl(ctx: *Context, decl: Decl.Index) !void {
    switch (ctx.decls.items[@enumToInt(decl)]) {
        .structure => |*structure| {
            std.debug.assert(structure.fields.entries.len == 0);
            var it = structure.syntax.fields(ctx.root);
            while (it.next(ctx.root)) |field| {
                const name_syntax = field.ident(ctx.root) orelse return error.Syntax;
                const name = ctx.root.tokenText(name_syntax);
                const type_syntax = field.typeExpr(ctx.root) orelse return error.Syntax;
                const ty = try ctx.analyzeTypeExpr(type_syntax);
                try structure.fields.put(ctx.allocator, name, ty);
            }
        },
        .function => |function| {
            var builder = ir.Builder{ .allocator = ctx.allocator };
            defer builder.func.deinit(ctx.allocator);
            const body = function.syntax.body(ctx.root) orelse return error.Syntax;
            builder.switchToBlock(try builder.addBlock());
            try ctx.genBlock(body, &builder);
            std.debug.print("{}\n", .{builder.func});
        },
        .constant => |*constant| {
            std.debug.assert(constant.ty == .invalid);
            const type_syntax = constant.syntax.typeExpr(ctx.root) orelse return error.Syntax;
            const ty = try ctx.analyzeTypeExpr(type_syntax);
            constant.ty = ty;
            //const expr = constant.syntax.expr(ctx.root) orelse return error.Syntax;
            //const ty = try ctx.analyzeExpr(expr);
        },
    }
}

fn analyzeExpr(ctx: *Context, expr: ast.Expr, expected_type: Type.Index) !Type.Index {
    switch (expr) {
        .literal => |literal| {
            if (literal.number(ctx.root)) |number| {
                _ = number;
                _ = expected_type;
            }
            return error.TypeInference;
        },
        inline else => |variant| {
            @panic("TODO: " ++ @typeName(@TypeOf(variant)));
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
            const decl = ctx.decls_by_name.get(ident_text) orelse return error.UndefinedIdentifier;
            return switch (ctx.decls.items[@enumToInt(decl)]) {
                .structure => |structure| structure.ty,
                inline else => |variant| {
                    @panic("TODO: " ++ @typeName(@TypeOf(variant)));
                },
            };
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
