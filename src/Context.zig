const std = @import("std");
const syntax = @import("syntax.zig");
const parse = @import("parse.zig");
const ir = @import("ir.zig");

const Context = @This();

allocator: std.mem.Allocator,
root: syntax.pure.Root,
ast: syntax.ast.File,
types: std.AutoArrayHashMapUnmanaged(Type.Key, Type) = .{},
structures: std.ArrayListUnmanaged(Struct) = .{},
functions: std.ArrayListUnmanaged(Fn) = .{},
diagnostics: std.MultiArrayList(Diagnostic) = .{},

const Diagnostic = struct {
    node: syntax.pure.Node.Index,
    message: []const u8,
};

fn addDiagnostic(ctx: *Context, node: syntax.pure.Node.Index, comptime fmt: []const u8, args: anytype) !void {
    return ctx.diagnostics.append(ctx.allocator, .{ .node = node, .message = try std.fmt.allocPrint(ctx.allocator, fmt, args) });
}

const FormatType = struct {
    ctx: *Context,
    ty: Type.Index,

    pub fn format(this: FormatType, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (this.ctx.typePtr(this.ty).*) {
            .invalid => try writer.print("invalid", .{}),
            .unsigned_integer => |unsigned_integer| try writer.print("u{}", .{unsigned_integer.bits}),
            .pointer_to => |pointee| try writer.print("*{}", .{this.ctx.formatType(pointee)}),
            .structure => |structure| try writer.print("{s}", .{this.ctx.structPtr(structure).name}),
            .function => |function| {
                try writer.print("fn {s}", .{this.ctx.fnPtr(function).name});
                {
                    try writer.print("(", .{});
                    var it = this.ctx.fnPtr(function).params.iterator();
                    var i: usize = 0;
                    while (it.next()) |entry| {
                        if (i > 0) try writer.print(", ", .{});
                        i += 1;
                        try writer.print("{s}: {}", .{ entry.key_ptr.*, this.ctx.formatType(entry.value_ptr.*) });
                    }
                    try writer.print(")", .{});
                }
                {
                    try writer.print(" (", .{});
                    var it = this.ctx.fnPtr(function).returns.iterator();
                    var i: usize = 0;
                    while (it.next()) |entry| {
                        if (i > 0) try writer.print(", ", .{});
                        i += 1;
                        try writer.print("{s}: {}", .{ entry.key_ptr.*, this.ctx.formatType(entry.value_ptr.*) });
                    }
                    try writer.print(")", .{});
                }
            },
        }
    }
};

fn formatType(
    ctx: *Context,
    ty: Type.Index,
) FormatType {
    return .{ .ctx = ctx, .ty = ty };
}

pub fn printDiagnostics(ctx: *Context, writer: anytype) !bool {
    for (ctx.diagnostics.items(.message)) |message| {
        try writer.print("error: {s}\n", .{message});
    }
    return ctx.diagnostics.len > 0;
}

pub fn dumpTypes(ctx: *Context) void {
    {
        var it = ctx.types.iterator();
        _ = it;
        for (ctx.types.keys(), 0..) |key, i|
            std.debug.print("{}: {}\n", .{ key, ctx.formatType(@intToEnum(Type.Index, i)) });
    }
    for (ctx.structures.items) |structure| {
        std.debug.print("struct {s} {{\n", .{structure.name});
        var it = structure.fields.iterator();
        while (it.next()) |entry| {
            std.debug.print("  {s}: {}\n", .{ entry.key_ptr.*, ctx.formatType(entry.value_ptr.*) });
        }
        std.debug.print("}}\n", .{});
    }
    for (ctx.functions.items) |function| {
        std.debug.print("fn {s}", .{function.name});
        {
            std.debug.print("(\n", .{});
            var it = function.params.iterator();
            while (it.next()) |entry| {
                std.debug.print("  {s}: {},\n", .{ entry.key_ptr.*, ctx.formatType(entry.value_ptr.*) });
            }
            std.debug.print(")", .{});
        }
        {
            std.debug.print(" (\n", .{});
            var it = function.returns.iterator();
            while (it.next()) |entry| {
                std.debug.print("  {s}: {},\n", .{ entry.key_ptr.*, ctx.formatType(entry.value_ptr.*) });
            }
            std.debug.print(")", .{});
        }
        std.debug.print(";\n", .{});
    }
}

const Type = union(enum) {
    invalid,
    unsigned_integer: struct { bits: u32 },
    pointer_to: Type.Index,
    structure: Struct.Index,
    function: Fn.Index,

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const Key = union(enum) {
        invalid,
        unsigned_integer: struct { bits: u32 },
        pointer_to: Type.Index,
        structure: syntax.ast.Decl.Struct,
        function: syntax.ast.Decl.Fn,

        pub fn format(this: Key, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            switch (this) {
                .invalid => try writer.print("invalid", .{}),
                .unsigned_integer => |unsigned_integer| try writer.print("uint(bits: {})", .{unsigned_integer.bits}),
                .pointer_to => |pointer_to| try writer.print("ptr(type: {})", .{@enumToInt(pointer_to)}),
                .structure => |structure| try writer.print("struct(ast: {})", .{@enumToInt(structure.tree)}),
                .function => |function| try writer.print("fn(ast: {})", .{@enumToInt(function.tree)}),
            }
        }
    };
};

const Struct = struct {
    analysis: enum { unanalyzed, analyzed } = .unanalyzed,
    syntax: syntax.ast.Decl.Struct,
    name: []const u8,
    fields: std.StringArrayHashMapUnmanaged(Type.Index) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

const Fn = struct {
    analysis: enum { unanalyzed, analyzed } = .unanalyzed,
    syntax: syntax.ast.Decl.Fn,
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(Type.Index) = .{},
    returns: std.StringArrayHashMapUnmanaged(Type.Index) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    const parsed = try parse.parseFile(allocator, src);
    return .{
        .allocator = allocator,
        .root = parsed.root,
        .ast = parsed.ast,
    };
}

pub fn deinit(ctx: *Context) void {
    for (ctx.diagnostics.items(.message)) |message|
        ctx.allocator.free(message);
    ctx.diagnostics.deinit(ctx.allocator);
    for (ctx.functions.items) |*function| {
        function.params.deinit(ctx.allocator);
        function.returns.deinit(ctx.allocator);
    }
    for (ctx.structures.items) |*structure|
        structure.fields.deinit(ctx.allocator);
    ctx.structures.deinit(ctx.allocator);
    ctx.functions.deinit(ctx.allocator);
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn analyze(ctx: *Context) !void {
    var names: std.StringHashMapUnmanaged(syntax.ast.Decl) = .{};
    defer names.deinit(ctx.allocator);

    {
        var it = ctx.ast.decls(ctx.root);
        while (it.next(ctx.root)) |decl_syntax| {
            const tree = switch (decl_syntax) {
                inline else => |s| syntax.ast.Decl.cast(ctx.root, s.tree),
            } orelse return error.Syntax;
            const ident = switch (decl_syntax) {
                inline else => |s| s.ident(ctx.root),
            } orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try names.put(ctx.allocator, name, tree);
        }
    }

    {
        var scope = Scope.File{ .names = &names };
        var it = names.iterator();
        while (it.next()) |entry| {
            try analyzeDecl(ctx, &scope.base, entry.value_ptr.*);
        }
    }
}

fn typePtr(ctx: *Context, i: Type.Index) *Type {
    return &ctx.types.values()[@enumToInt(i)];
}

fn structPtr(ctx: *Context, i: Struct.Index) *Struct {
    return &ctx.structures.items[@enumToInt(i)];
}

fn fnPtr(ctx: *Context, i: Fn.Index) *Fn {
    return &ctx.functions.items[@enumToInt(i)];
}

fn analyzeDecl(ctx: *Context, scope: *const Scope, decl: syntax.ast.Decl) !void {
    std.debug.print("analyzeDecl: {}\n", .{decl});
    switch (decl) {
        .structure => |struct_syntax| {
            var type_index = try ctx.lookUpType(.{ .structure = struct_syntax });
            var struct_index = typePtr(ctx, type_index).structure;
            var structure = structPtr(ctx, struct_index);
            if (structure.analysis == .unanalyzed) {
                std.debug.assert(structure.fields.entries.len == 0);
                var it = struct_syntax.fields(ctx.root);
                while (it.next(ctx.root)) |field| {
                    const name_syntax = field.ident(ctx.root) orelse return error.Syntax;
                    const name = ctx.root.tokenText(name_syntax);
                    const type_syntax = field.typeExpr(ctx.root) orelse return error.Syntax;
                    const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                    try structure.fields.put(ctx.allocator, name, ty);
                }
                structure.analysis = .analyzed;
            }
        },
        .function => |function_syntax| {
            var type_index = try ctx.lookUpType(.{ .function = function_syntax });
            var function_index = typePtr(ctx, type_index).function;
            var function = fnPtr(ctx, function_index);
            if (function.analysis == .unanalyzed) {
                params: {
                    const params = function_syntax.params(ctx.root) orelse break :params;
                    var it = params.params(ctx.root);
                    while (it.next(ctx.root)) |param| {
                        const name_syntax = param.ident(ctx.root) orelse return error.Syntax;
                        const name = ctx.root.tokenText(name_syntax);
                        const type_syntax = param.typeExpr(ctx.root) orelse return error.Syntax;
                        const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                        try function.params.put(ctx.allocator, name, ty);
                    }
                }
                returns: {
                    const returns = function_syntax.returns(ctx.root) orelse break :returns;
                    var it = returns.returns(ctx.root);
                    while (it.next(ctx.root)) |param| {
                        const name_syntax = param.ident(ctx.root) orelse return error.Syntax;
                        const name = ctx.root.tokenText(name_syntax);
                        const type_syntax = param.typeExpr(ctx.root) orelse return error.Syntax;
                        const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                        try function.returns.put(ctx.allocator, name, ty);
                    }
                }
                function.analysis = .analyzed;
            }
        },
        .constant => |constant_syntax| {
            const type_expr = constant_syntax.typeExpr(ctx.root) orelse return error.Syntax;
            const ty = try ctx.analyzeTypeExpr(scope, type_expr);
            const expr = constant_syntax.expr(ctx.root) orelse return error.Syntax;
            const expr_ty = try ctx.analyzeExpr(scope, expr, ty);
            if (ty != expr_ty) {
                try ctx.addDiagnostic(
                    syntax.pure.Node.Index.fromTree(constant_syntax.tree),
                    "type mismatch: expected {}, got {}",
                    .{ ctx.formatType(ty), ctx.formatType(expr_ty) },
                );
            }
        },
    }
}

fn typeOfDecl(ctx: *Context, root_scope: *const Scope, decl: syntax.ast.Decl) !Type.Index {
    std.debug.print("analyzeDecl: {}\n", .{decl});
    switch (decl) {
        .structure => |struct_syntax| {
            return ctx.lookUpType(.{ .structure = struct_syntax });
        },
        .function => |function_syntax| {
            return ctx.lookUpType(.{ .function = function_syntax });
        },
        .constant => |constant_syntax| {
            const type_expr = constant_syntax.typeExpr(ctx.root) orelse return error.Syntax;
            return try ctx.analyzeTypeExpr(root_scope, type_expr);
        },
    }
}

// may return a type other than/incompatible with expected_type
fn analyzeExpr(ctx: *Context, scope: *const Scope, expr: syntax.ast.Expr, expected_type: Type.Index) !Type.Index {
    switch (expr) {
        .literal => |literal| {
            if (literal.number(ctx.root)) |_| {
                if (ctx.typePtr(expected_type).* == .unsigned_integer)
                    return expected_type;
                if (ctx.typePtr(expected_type).* == .pointer_to)
                    return expected_type;
                return error.TypeMismatch;
            }

            return error.TypeInference;
        },
        .ident => |ident_expr| {
            const name = ctx.root.tokenText(ident_expr.ident(ctx.root) orelse return error.Syntax);
            const tree = scope.get(name) orelse return error.UndefinedIdentifier;
            const decl = syntax.ast.Decl.cast(ctx.root, tree) orelse return error.Syntax;
            const root_scope = scope; // TODO
            return typeOfDecl(ctx, root_scope, decl);
        },
        .binary => |binary_expr| {
            const lhs_expr = binary_expr.lhs(ctx.root) orelse return error.Syntax;
            const rhs_expr = binary_expr.rhs(ctx.root) orelse return error.Syntax;
            const lhs_type = try analyzeExpr(ctx, scope, lhs_expr, expected_type);
            const rhs_type = try analyzeExpr(ctx, scope, rhs_expr, expected_type);
            if (binary_expr.plus(ctx.root) != null) {
                if (lhs_type == rhs_type)
                    return lhs_type;
            }
            return error.TODO;
        },
        inline else => |variant| {
            @panic("TODO: " ++ @typeName(@TypeOf(variant)));
        },
    }
}

const Scope = struct {
    parent: ?*Scope,
    getFn: *const fn (self: *const Scope, name: []const u8) ?syntax.pure.Tree.Index,

    pub fn get(scope: *const Scope, name: []const u8) ?syntax.pure.Tree.Index {
        if (scope.getFn(scope, name)) |i| return i;
        if (scope.parent) |p| return p.get(name);
        return null;
    }

    const File = struct {
        base: Scope = .{
            .parent = null,
            .getFn = File.get,
        },
        names: *const std.StringHashMapUnmanaged(syntax.ast.Decl),

        fn get(scope: *const Scope, name: []const u8) ?syntax.pure.Tree.Index {
            const file = @fieldParentPtr(File, "base", scope);
            const decl = file.names.get(name) orelse return null;
            switch (decl) {
                inline else => |s| return s.tree,
            }
        }
    };
};

fn lookUpType(ctx: *Context, key: Type.Key) !Type.Index {
    if (ctx.types.getIndex(key)) |i| return @intToEnum(Type.Index, i);
    switch (key) {
        .unsigned_integer => |unsigned_integer| {
            const i = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .unsigned_integer = .{ .bits = unsigned_integer.bits } });
            return @intToEnum(Type.Index, i);
        },
        .structure => |structure| {
            const struct_index = ctx.structures.items.len;
            const ident = structure.ident(ctx.root) orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try ctx.structures.append(ctx.allocator, .{ .syntax = structure, .name = name });
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .structure = @intToEnum(Struct.Index, struct_index) });
            return @intToEnum(Type.Index, type_index);
        },
        .function => |function| {
            const function_index = ctx.functions.items.len;
            const ident = function.ident(ctx.root) orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try ctx.functions.append(ctx.allocator, .{ .syntax = function, .name = name });
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .function = @intToEnum(Fn.Index, function_index) });
            return @intToEnum(Type.Index, type_index);
        },
        .pointer_to => |pointee| {
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .pointer_to = pointee });
            return @intToEnum(Type.Index, type_index);
        },
        inline else => |variant| {
            @panic("TODO: " ++ @typeName(@TypeOf(variant)));
        },
    }
}

fn analyzeTypeExpr(ctx: *Context, scope: *const Scope, type_expr: syntax.ast.TypeExpr) !Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = ident.ident(ctx.root) orelse return error.Syntax;
            const ident_text = ctx.root.tokenText(ident_token);
            if (ident_text.len > 0 and ident_text[0] == 'u') {
                if (std.fmt.parseInt(u32, ident_text[1..], 10)) |bits| {
                    return ctx.lookUpType(.{ .unsigned_integer = .{ .bits = bits } });
                } else |_| {}
            }
            const decl_tree = scope.get(ident_text) orelse return error.UndefinedIdentifier;
            const decl = syntax.ast.Decl.cast(ctx.root, decl_tree) orelse return error.Syntax;
            switch (decl) {
                .structure => |structure| {
                    return ctx.lookUpType(.{ .structure = structure });
                },
                inline else => |other| {
                    @panic("TODO: " ++ @typeName(@TypeOf(other)));
                },
            }
        },
        .unary => |unary| {
            const operand_type_expr = unary.typeExpr(ctx.root) orelse return error.Syntax;
            const operand_type_index = try analyzeTypeExpr(ctx, scope, operand_type_expr);

            if (unary.star(ctx.root) != null)
                return ctx.lookUpType(.{ .pointer_to = operand_type_index });

            return error.TODO;
        },
    }
}

fn genBlock(ctx: *Context, block: syntax.ast.Stmt.Block, builder: *ir.Builder) !void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        const child_tree = child.asTree() orelse continue;
        const stmt = syntax.ast.Stmt.cast(ctx.root, child_tree) orelse return error.Syntax;
        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = expr_stmt.expr(ctx.root) orelse return error.Syntax;
                _ = try genExpr(ctx, expr, builder);
            },
            .block => |nested_block| {
                return ctx.genBlock(nested_block, builder);
            },
            .@"return" => |return_stmt| {
                const expr = return_stmt.expr(ctx.root) orelse return error.Syntax;
                const value = try genExpr(ctx, expr, builder);
                try builder.buildRet(value.reg);
            },
        }
    }
}

const Value = union(enum) {
    reg: ir.Reg,
};

fn genExpr(ctx: *Context, expr: syntax.ast.Expr, builder: *ir.Builder) !Value {
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
            return genExpr(ctx, inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse return error.Syntax;
            // TODO
            return genExpr(ctx, inner, builder);
        },
        .ident => |ident| {
            _ = ident;
            //ctx.lookUpScope(.{ .decl = decl });
            return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = 0 }) };
        },
    }
}

fn genBinExpr(ctx: *Context, expr: syntax.ast.Expr.Binary, builder: *ir.Builder, op: enum { add, sub, mul, div, rem }) !Value {
    const lhs = expr.lhs(ctx.root) orelse return error.Syntax;
    const rhs = expr.rhs(ctx.root) orelse return error.Syntax;
    const lhs_value = try genExpr(ctx, lhs, builder);
    const rhs_value = try genExpr(ctx, rhs, builder);
    return switch (op) {
        .add => .{ .reg = try builder.buildAdd(lhs_value.reg, rhs_value.reg) },
        .sub => unreachable, //.{ .reg = try builder.buildSub(lhs_value.reg, rhs_value.reg) },
        .mul => unreachable, //.{ .reg = try builder.buildMul(lhs_value.reg, rhs_value.reg) },
        .div => unreachable, //.{ .reg = try builder.buildDiv(lhs_value.reg, rhs_value.reg) },
        .rem => unreachable, //.{ .reg = try builder.buildRem(lhs_value.reg, rhs_value.reg) },
    };
}
