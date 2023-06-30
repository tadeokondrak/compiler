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
    //std.debug.print(fmt, args);
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
            .function => |function_index| {
                const function = this.ctx.fnPtr(function_index);
                try writer.print("fn {s}(", .{function.name});
                for (function.params.keys(), function.params.values(), 0..) |key, value, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try writer.print("{s}: {}", .{ key, this.ctx.formatType(value) });
                }
                try writer.print(") (", .{});
                for (function.returns.keys(), function.returns.values(), 0..) |key, value, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try writer.print("{s}: {}", .{ key, this.ctx.formatType(value) });
                }
                try writer.print(")", .{});
            },
        }
    }
};

fn formatType(ctx: *Context, ty: Type.Index) FormatType {
    return .{ .ctx = ctx, .ty = ty };
}

pub fn printDiagnostics(ctx: *Context, writer: anytype) !bool {
    for (ctx.diagnostics.items(.message)) |message|
        try writer.print("error: {s}\n", .{message});
    return ctx.diagnostics.len > 0;
}

pub fn dumpTypes(ctx: *Context) void {
    for (ctx.types.keys(), 0..) |key, i|
        std.debug.print("{}: {}\n", .{ key, ctx.formatType(@enumFromInt(i)) });
    for (ctx.structures.items) |structure| {
        std.debug.print("struct {s} {{\n", .{structure.name});
        var it = structure.fields.iterator();
        while (it.next()) |entry| {
            std.debug.print("  {s}: {}\n", .{ entry.key_ptr.*, ctx.formatType(entry.value_ptr.*) });
        }
        std.debug.print("}}\n", .{});
    }
    for (ctx.functions.items) |function| {
        std.debug.print("fn {s}(", .{function.name});
        for (function.params.keys(), function.params.values(), 0..) |key, value, i| {
            if (i > 0) std.debug.print(", ", .{});
            std.debug.print("{s}: {}", .{ key, ctx.formatType(value) });
        }
        std.debug.print(") (", .{});
        for (function.returns.keys(), function.returns.values(), 0..) |key, value, i| {
            if (i > 0) std.debug.print(", ", .{});
            std.debug.print("{s}: {}", .{ key, ctx.formatType(value) });
        }
        std.debug.print(") {{\n", .{});
        if (function.analysis == .generated) {
            std.debug.print("{}", .{function.func});
        }
        std.debug.print("}}\n", .{});
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
    analysis: enum { unanalyzed, analyzed, generated } = .unanalyzed,
    syntax: syntax.ast.Decl.Fn,
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(Type.Index) = .{},
    returns: std.StringArrayHashMapUnmanaged(Type.Index) = .{},
    func: ir.Func = undefined,

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
        if (function.analysis == .generated) {
            function.func.deinit(ctx.allocator);
        }
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

pub fn compile(ctx: *Context) !void {
    var names: std.StringArrayHashMapUnmanaged(syntax.ast.Decl) = .{};
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

    var scope = Scope.File{ .names = &names };
    for (names.values()) |value|
        try analyzeDecl(ctx, &scope.base, value);

    for (names.values()) |decl| {
        switch (decl) {
            .function => |function_syntax| {
                var type_index = try ctx.lookUpType(.{ .function = function_syntax });
                var function_index = typePtr(ctx, type_index).function;
                var function = fnPtr(ctx, function_index);
                std.debug.assert(function.analysis == .analyzed);
                const body = function_syntax.body(ctx.root) orelse return error.Syntax;
                var builder: ir.Builder = .{ .allocator = ctx.allocator };
                {
                    errdefer builder.func.deinit(ctx.allocator);
                    builder.switchToBlock(try builder.addBlock());
                    try genBlock(ctx, body, &builder);
                }
                function.func = builder.func;
                function.analysis = .generated;
            },
            else => {},
        }
    }
}

fn typePtr(ctx: *Context, i: Type.Index) *Type {
    return &ctx.types.values()[@intFromEnum(i)];
}

fn structPtr(ctx: *Context, i: Struct.Index) *Struct {
    return &ctx.structures.items[@intFromEnum(i)];
}

fn fnPtr(ctx: *Context, i: Fn.Index) *Fn {
    return &ctx.functions.items[@intFromEnum(i)];
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
                try ctx.checkFnBody(scope, function_index);
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
fn analyzeExpr(ctx: *Context, scope: *const Scope, expr: syntax.ast.Expr, expected_type: ?Type.Index) !Type.Index {
    switch (expr) {
        .literal => |literal| {
            if (literal.number(ctx.root)) |_| {
                if (expected_type) |present_expected_type| {
                    if (ctx.typePtr(present_expected_type).* == .unsigned_integer)
                        return present_expected_type;
                    if (ctx.typePtr(present_expected_type).* == .pointer_to)
                        return present_expected_type;

                    return error.TypeMismatch;
                } else {
                    return ctx.lookUpType(.{ .unsigned_integer = .{ .bits = 32 } });
                }
            }

            return error.TypeInference;
        },
        .ident => |ident_expr| {
            const name = ctx.root.tokenText(ident_expr.ident(ctx.root) orelse return error.Syntax);
            const tree = scope.get(name) orelse {
                try ctx.addDiagnostic(syntax.pure.Node.Index.fromTree(ident_expr.tree), "undefined identifier: {s}", .{name});
                return error.Syntax;
            };
            if (syntax.ast.Decl.cast(ctx.root, tree)) |decl| {
                const root_scope = scope; // TODO
                return typeOfDecl(ctx, root_scope, decl);
            }
            if (syntax.ast.Decl.Fn.Param.cast(ctx.root, tree)) |param| {
                const type_expr = param.typeExpr(ctx.root) orelse return error.Syntax;
                return try ctx.analyzeTypeExpr(scope, type_expr);
            }
            return error.Syntax;
        },
        .binary => |binary_expr| {
            const lhs_expr = binary_expr.lhs(ctx.root) orelse return error.Syntax;
            const rhs_expr = binary_expr.rhs(ctx.root) orelse return error.Syntax;
            const lhs_type = try analyzeExpr(ctx, scope, lhs_expr, null);
            const rhs_type = try analyzeExpr(ctx, scope, rhs_expr, null);
            if (binary_expr.plus(ctx.root) != null or
                binary_expr.minus(ctx.root) != null)
            {
                if (lhs_type == rhs_type)
                    return lhs_type;
                try ctx.addDiagnostic(
                    syntax.pure.Node.Index.fromTree(binary_expr.tree),
                    "arithmetic operator type mismatch: lhs {}, rhs {}",
                    .{ ctx.formatType(lhs_type), ctx.formatType(rhs_type) },
                );
                return ctx.lookUpType(.invalid);
            }
            if (binary_expr.lt_eq(ctx.root) != null) {
                if (lhs_type == rhs_type)
                    return ctx.lookUpType(.{ .unsigned_integer = .{ .bits = 1 } });
                try ctx.addDiagnostic(
                    syntax.pure.Node.Index.fromTree(binary_expr.tree),
                    "comparison operator type mismatch: lhs {}, rhs {}",
                    .{ ctx.formatType(lhs_type), ctx.formatType(rhs_type) },
                );
                return ctx.lookUpType(.invalid);
            }
            return error.TODO;
        },
        .call => |call_expr| {
            const fn_expr = call_expr.expr(ctx.root) orelse return error.Syntax;
            const fn_type_index = try analyzeExpr(ctx, scope, fn_expr, null);
            const fn_type = ctx.typePtr(fn_type_index);
            if (fn_type.* != .function) return error.TODO;
            const function = ctx.fnPtr(fn_type.function);
            const params = function.params;
            const args_wrapper = call_expr.args(ctx.root) orelse return error.Syntax;
            var args = args_wrapper.args(ctx.root);
            for (params.values()) |param_type| {
                const arg = args.next(ctx.root) orelse return error.TODO;
                const arg_expr = arg.expr(ctx.root) orelse return error.TODO;
                const arg_type = try analyzeExpr(ctx, scope, arg_expr, null);
                if (arg_type != param_type) return error.TODO;
            }
            if (args.next(ctx.root)) |_| return error.TODO;

            // TODO
            std.debug.assert(function.returns.values().len == 1);
            const ret_type = function.returns.values()[0];
            return ret_type;
        },
        inline else => |variant| {
            @panic("TODO: " ++ @typeName(@TypeOf(variant)));
        },
    }
}

const Scope = struct {
    parent: ?*const Scope,
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
        names: *const std.StringArrayHashMapUnmanaged(syntax.ast.Decl),

        fn get(scope: *const Scope, name: []const u8) ?syntax.pure.Tree.Index {
            const file = @fieldParentPtr(File, "base", scope);
            const decl = file.names.get(name) orelse return null;
            switch (decl) {
                inline else => |s| return s.tree,
            }
        }
    };

    const Fn = struct {
        base: Scope = .{
            .parent = null,
            .getFn = Scope.Fn.get,
        },
        args: *const std.StringArrayHashMapUnmanaged(syntax.ast.Decl.Fn.Param),

        fn get(scope: *const Scope, name: []const u8) ?syntax.pure.Tree.Index {
            const function = @fieldParentPtr(Scope.Fn, "base", scope);
            const param = function.args.get(name) orelse return null;
            return param.tree;
        }
    };
};

fn lookUpType(ctx: *Context, key: Type.Key) !Type.Index {
    if (ctx.types.getIndex(key)) |i| return @enumFromInt(i);
    switch (key) {
        .invalid => {
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .invalid);
            return @enumFromInt(type_index);
        },
        .unsigned_integer => |unsigned_integer| {
            const i = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .unsigned_integer = .{ .bits = unsigned_integer.bits } });
            return @enumFromInt(i);
        },
        .structure => |structure| {
            const struct_index = ctx.structures.items.len;
            const ident = structure.ident(ctx.root) orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try ctx.structures.append(ctx.allocator, .{ .syntax = structure, .name = name });
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .structure = @enumFromInt(struct_index) });
            return @enumFromInt(type_index);
        },
        .function => |function| {
            const function_index = ctx.functions.items.len;
            const ident = function.ident(ctx.root) orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try ctx.functions.append(ctx.allocator, .{ .syntax = function, .name = name });
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .function = @enumFromInt(function_index) });
            return @enumFromInt(type_index);
        },
        .pointer_to => |pointee| {
            const type_index = ctx.types.entries.len;
            try ctx.types.put(ctx.allocator, key, .{ .pointer_to = pointee });
            return @enumFromInt(type_index);
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

            try ctx.addDiagnostic(syntax.pure.Node.Index.fromTree(unary.tree), "unknown binary operator", .{});

            return ctx.lookUpType(.invalid);
        },
    }
}

fn checkFnBody(ctx: *Context, scope: *const Scope, function: Fn.Index) !void {
    const body = ctx.fnPtr(function).syntax.body(ctx.root) orelse return error.Syntax;

    var args: std.StringArrayHashMapUnmanaged(syntax.ast.Decl.Fn.Param) = .{};
    defer args.deinit(ctx.allocator);

    const params = ctx.fnPtr(function).syntax.params(ctx.root) orelse return error.Syntax;
    var it = params.params(ctx.root);
    while (it.next(ctx.root)) |param| {
        const name_syntax = param.ident(ctx.root) orelse return error.Syntax;
        const name = ctx.root.tokenText(name_syntax);
        try args.put(ctx.allocator, name, param);
    }

    const fn_scope: Scope.Fn = .{ .base = .{ .parent = scope, .getFn = Scope.Fn.get }, .args = &args };
    try ctx.checkBlock(&fn_scope.base, function, body);
}

fn checkBlock(ctx: *Context, scope: *const Scope, function: Fn.Index, body: syntax.ast.Stmt.Block) !void {
    for (ctx.root.treeChildren(body.tree)) |child| {
        const child_tree = child.asTree() orelse continue;
        const stmt = syntax.ast.Stmt.cast(ctx.root, child_tree) orelse return error.Syntax;
        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = expr_stmt.expr(ctx.root) orelse return error.Syntax;
                try checkExpr(ctx, scope, function, expr);
            },
            .block => |block_stmt| {
                try ctx.checkBlock(scope, function, block_stmt);
            },
            .@"return" => |return_stmt| {
                const returns = &ctx.fnPtr(function).returns;
                var exprs = return_stmt.exprs(ctx.root);
                for (returns.values()) |declared_type| {
                    const expr = exprs.next(ctx.root) orelse return error.Syntax;
                    try checkExpr(ctx, scope, function, expr);
                    const inferred_type = try ctx.analyzeExpr(scope, expr, null);
                    if (inferred_type != declared_type)
                        try ctx.addDiagnostic(undefined, "return type mismatch: declared {}, inferred {}", .{
                            ctx.formatType(inferred_type),
                            ctx.formatType(declared_type),
                        });
                }
                if (exprs.next(ctx.root)) |_| {
                    try ctx.addDiagnostic(undefined, "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                const cond = if_stmt.cond(ctx.root) orelse return error.Syntax;
                try checkExpr(ctx, scope, function, cond);
                const bool_type = try ctx.lookUpType(.{ .unsigned_integer = .{ .bits = 1 } });
                const cond_type = try ctx.analyzeExpr(scope, cond, bool_type);
                if (cond_type != bool_type)
                    try ctx.addDiagnostic(undefined, "condition must be boolean", .{});
                const if_body = if_stmt.body(ctx.root) orelse return error.Syntax;
                try ctx.checkBlock(scope, function, if_body);
            },
        }
    }
}

fn checkExpr(ctx: *Context, scope: *const Scope, function: Fn.Index, expr: syntax.ast.Expr) !void {
    _ = ctx;
    _ = scope;
    _ = function;
    switch (expr) {
        else => {},
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
                var exprs = return_stmt.exprs(ctx.root);
                if (exprs.next(ctx.root)) |expr| {
                    if (exprs.next(ctx.root) != null)
                        return error.TODO;
                    const first_value = try genExpr(ctx, expr, builder);
                    return builder.buildRetVal(first_value.reg);
                } else {
                    return builder.buildRetVoid();
                }
            },
            .@"if" => |if_stmt| {
                const cond = if_stmt.cond(ctx.root) orelse return error.Syntax;
                const cond_value = try genExpr(ctx, cond, builder);
                const then_block = try builder.addBlock();
                const cont_block = try builder.addBlock();
                try builder.buildBranch(cond_value.reg, then_block, cont_block);
                builder.switchToBlock(then_block);
                const if_body = if_stmt.body(ctx.root) orelse return error.Syntax;
                try ctx.genBlock(if_body, builder);
                try builder.buildJump(cont_block);
                builder.switchToBlock(cont_block);
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
            if (binary_expr.lt_eq(ctx.root) != null) return genBinExpr(ctx, binary_expr, builder, .lt_eq);
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

fn genBinExpr(ctx: *Context, expr: syntax.ast.Expr.Binary, builder: *ir.Builder, op: enum { add, sub, mul, div, rem, lt_eq }) !Value {
    const lhs = expr.lhs(ctx.root) orelse return error.Syntax;
    const rhs = expr.rhs(ctx.root) orelse return error.Syntax;
    const lhs_value = try genExpr(ctx, lhs, builder);
    const rhs_value = try genExpr(ctx, rhs, builder);
    return switch (op) {
        .add => .{ .reg = try builder.buildArith(.add, lhs_value.reg, rhs_value.reg) },
        .sub => .{ .reg = try builder.buildArith(.sub, lhs_value.reg, rhs_value.reg) },
        .mul => .{ .reg = try builder.buildArith(.mul, lhs_value.reg, rhs_value.reg) },
        .div => .{ .reg = try builder.buildArith(.div, lhs_value.reg, rhs_value.reg) },
        .rem => .{ .reg = try builder.buildArith(.rem, lhs_value.reg, rhs_value.reg) },
        .lt_eq => .{ .reg = try builder.buildCmp(.lt_eq, lhs_value.reg, rhs_value.reg) },
    };
}
