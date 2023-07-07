const Context = @This();

const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");
const ir = @import("ir.zig");
const LineIndex = @import("LineIndex.zig");

allocator: std.mem.Allocator,
root: syntax.pure.Root,
ast: syntax.ast.File,
types: std.AutoArrayHashMapUnmanaged(void, Type) = .{},
structures: std.ArrayListUnmanaged(Struct) = .{},
functions: std.ArrayListUnmanaged(Fn) = .{},
diagnostics: std.MultiArrayList(Diagnostic) = .{},

const Diagnostic = struct {
    span: syntax.pure.Span,
    message: []const u8,
};

fn addDiagnostic(ctx: *Context, span: syntax.pure.Span, comptime fmt: []const u8, args: anytype) !void {
    return ctx.diagnostics.append(ctx.allocator, .{ .span = span, .message = try std.fmt.allocPrint(ctx.allocator, fmt, args) });
}

const FormatFnArgs = struct { ctx: *Context, function: Fn.Index };

fn formatFn(args: FormatFnArgs, comptime fmt: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
    const function = args.ctx.fnPtr(args.function);
    try writer.print("fn {s}(", .{function.name});
    for (function.params.keys(), function.params.values(), 0..) |key, value, i| {
        if (i > 0) try writer.print(", ", .{});
        try writer.print("{s}: {}", .{ key, args.ctx.fmtType(value.ty) });
    }
    try writer.print(") (", .{});
    for (function.returns.keys(), function.returns.values(), 0..) |key, value, i| {
        if (i > 0) try writer.print(", ", .{});
        try writer.print("{s}: {}", .{ key, args.ctx.fmtType(value.ty) });
    }
    try writer.print(")", .{});
    if (std.mem.eql(u8, fmt, "code") and function.analysis == .generated) {
        try writer.print(" {{\n{}\n}}", .{function.func});
    }
}

fn fmtFn(ctx: *Context, function: Fn.Index) std.fmt.Formatter(formatFn) {
    return .{ .data = .{ .ctx = ctx, .function = function } };
}

const FormatStructArgs = struct { ctx: *Context, structure: Struct.Index };

fn formatStruct(args: FormatStructArgs, comptime fmt: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
    const structure = args.ctx.structPtr(args.structure);
    if (std.mem.eql(u8, fmt, "#")) {
        try writer.print("struct {s}", .{structure.name});
        try writer.print(" {{", .{});
        for (structure.fields.keys(), structure.fields.values(), 0..) |key, value, i| {
            if (i > 0) try writer.print(",", .{});
            try writer.print(" {s}: {}", .{ key, args.ctx.fmtType(value) });
        }
        try writer.print(" }}", .{});
    } else {
        try writer.writeAll(structure.name);
    }
}

fn fmtStruct(ctx: *Context, structure: Struct.Index) std.fmt.Formatter(formatStruct) {
    return .{ .data = .{ .ctx = ctx, .structure = structure } };
}

const FormatTypeArgs = struct { ctx: *Context, ty: Type.Index };

fn formatType(args: FormatTypeArgs, comptime fmt: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
    return switch (args.ctx.typePtr(args.ty).*) {
        .invalid => writer.print("invalid", .{}),
        .bool => writer.print("bool", .{}),
        .unsigned_integer => |unsigned_integer| writer.print("u{}", .{unsigned_integer.bits}),
        .pointer_to => |pointee| writer.print("*{}", .{args.ctx.fmtType(pointee)}),
        .structure => |structure| args.ctx.fmtStruct(structure).format(fmt, .{}, writer),
        .function => |function| args.ctx.fmtFn(function).format(fmt, .{}, writer),
    };
}

fn fmtType(ctx: *Context, ty: Type.Index) std.fmt.Formatter(formatType) {
    return .{ .data = .{ .ctx = ctx, .ty = ty } };
}

pub fn printDiagnostics(ctx: *Context, src: []const u8, writer: anytype) !bool {
    if (ctx.diagnostics.len == 0)
        return false;
    const line_index = try LineIndex.make(ctx.allocator, src);
    defer line_index.deinit(ctx.allocator);
    for (ctx.diagnostics.items(.span), ctx.diagnostics.items(.message)) |span, message| {
        const start = line_index.translate(span.start.offset);
        const end = line_index.translate(span.end.offset);
        const len = if (start.line != end.line) 1 else end.col - start.col;
        try writer.print("<input>:{}:{}: {s}\n", .{ start.line + 1, start.col + 1, message });
        const line_start = line_index.newlines[start.line - 1] + 1;
        const line_end = line_index.newlines[start.line];
        const line = src[line_start..line_end];
        for (line) |c| {
            try writer.writeByte(c);
        }
        try writer.writeByte('\n');
        for (0..start.col) |_|
            try writer.writeByte(' ');
        for (0..len) |_|
            try writer.writeByte('^');
        try writer.writeByte('\n');
    }
    return true;
}

pub fn dump(ctx: *Context, writer: anytype) !void {
    for (0..ctx.types.entries.len) |i|
        try writer.print("Type {}: {#}\n", .{ i, ctx.fmtType(@enumFromInt(i)) });
    for (0..ctx.functions.items.len) |i|
        try writer.print("{code}\n", .{ctx.fmtFn(@enumFromInt(i))});
}

const Type = union(enum) {
    invalid,
    bool,
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
        bool,
        unsigned_integer: struct { bits: u32 },
        pointer_to: Type.Index,
        structure: syntax.ast.Decl.Struct,
        function: syntax.ast.Decl.Fn,
    };

    fn toKey(ctx: *Context, ty: Type) Key {
        return switch (ty) {
            .invalid => .invalid,
            .bool => .bool,
            .unsigned_integer => |unsigned_integer| .{ .unsigned_integer = .{ .bits = unsigned_integer.bits } },
            .pointer_to => |pointee| .{ .pointer_to = pointee },
            .structure => |structure| .{ .structure = ctx.structPtr(structure).syntax },
            .function => |function| .{ .function = ctx.fnPtr(function).syntax },
        };
    }

    const HashContext = struct {
        ctx: *Context,

        pub fn hash(_: @This(), key: Key) u32 {
            var hasher = std.hash.Wyhash.init(0);
            std.hash.autoHash(&hasher, key);
            return @truncate(hasher.final());
        }

        pub fn eql(self: @This(), key: Key, _: void, b_index: usize) bool {
            const other_key = toKey(self.ctx, self.ctx.types.values()[b_index]);
            return std.meta.eql(key, other_key);
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
    analysis: enum { unanalyzed, analyzed, generated } = .unanalyzed,
    syntax: syntax.ast.Decl.Fn,
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(struct { syntax: syntax.pure.Tree.Index, ty: Type.Index }) = .{},
    returns: std.StringArrayHashMapUnmanaged(struct { syntax: syntax.pure.Tree.Index, ty: Type.Index }) = .{},
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
        if (function.analysis == .generated)
            function.func.deinit(ctx.allocator);
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
            const ident = switch (decl_syntax) {
                inline else => |s| s.ident(ctx.root),
            } orelse return error.Syntax;
            const name = ctx.root.tokenText(ident);
            try names.put(ctx.allocator, name, decl_syntax);
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
                var args: std.StringArrayHashMapUnmanaged(syntax.pure.Tree.Index) = .{};
                defer args.deinit(ctx.allocator);
                var fn_scope = Scope.Fn{ .base = .{ .parent = &scope.base, .getFn = Scope.Fn.get }, .args = &args };
                var gen = Gen{};
                defer gen.vars.deinit(ctx.allocator);
                {
                    errdefer builder.func.deinit(ctx.allocator);
                    var params: std.ArrayListUnmanaged(ir.Block.Param) = .{};
                    defer params.deinit(ctx.allocator);
                    for (function.params.keys(), function.params.values()) |name, param| {
                        const reg = builder.addReg();
                        try params.append(ctx.allocator, .{
                            .ty = try ctx.irType(param.ty),
                            .reg = reg,
                        });
                        try args.put(ctx.allocator, name, param.syntax);
                        try gen.vars.put(ctx.allocator, param.syntax, reg);
                    }
                    builder.switchToBlock(try builder.addBlock(params.items));
                    try genBlock(ctx, &gen, &fn_scope.base, body, &builder);
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
                        try function.params.put(ctx.allocator, name, .{
                            .syntax = param.tree,
                            .ty = ty,
                        });
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
                        try function.returns.put(ctx.allocator, name, .{
                            .syntax = param.tree,
                            .ty = ty,
                        });
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
                    ctx.root.treeSpan(expr.tree()),
                    "expected {}, got {}",
                    .{ ctx.fmtType(ty), ctx.fmtType(expr_ty) },
                );
            }
        },
    }
}

fn typeOfDecl(ctx: *Context, root_scope: *const Scope, decl: syntax.ast.Decl) !Type.Index {
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
                try ctx.addDiagnostic(ctx.root.treeSpan(ident_expr.tree), "undefined identifier: {s}", .{name});
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
                binary_expr.minus(ctx.root) != null or
                binary_expr.star(ctx.root) != null or
                binary_expr.slash(ctx.root) != null or
                binary_expr.percent(ctx.root) != null or
                binary_expr.lt2(ctx.root) != null or
                binary_expr.gt2(ctx.root) != null or
                binary_expr.ampersand(ctx.root) != null or
                binary_expr.pipe(ctx.root) != null or
                binary_expr.caret(ctx.root) != null)
            {
                if (lhs_type == rhs_type)
                    return lhs_type;
                try ctx.addDiagnostic(
                    ctx.root.treeSpan(binary_expr.tree),
                    "arithmetic operator type mismatch: lhs {}, rhs {}",
                    .{ ctx.fmtType(lhs_type), ctx.fmtType(rhs_type) },
                );
                return ctx.lookUpType(.invalid);
            }
            if (binary_expr.eq2(ctx.root) != null or
                binary_expr.bangEq(ctx.root) != null or
                binary_expr.lt(ctx.root) != null or
                binary_expr.ltEq(ctx.root) != null or
                binary_expr.gt(ctx.root) != null or
                binary_expr.gtEq(ctx.root) != null)
            {
                if (lhs_type == rhs_type)
                    return ctx.lookUpType(.bool);
                try ctx.addDiagnostic(
                    ctx.root.treeSpan(binary_expr.tree),
                    "comparison operator type mismatch: lhs {}, rhs {}",
                    .{ ctx.fmtType(lhs_type), ctx.fmtType(rhs_type) },
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
            for (params.values()) |param| {
                const arg = args.next(ctx.root) orelse return error.TODO;
                const arg_expr = arg.expr(ctx.root) orelse return error.TODO;
                const arg_type = try analyzeExpr(ctx, scope, arg_expr, null);
                if (arg_type != param.ty) return error.TODO;
            }
            if (args.next(ctx.root)) |_| return error.TODO;

            // TODO
            std.debug.assert(function.returns.values().len == 1);
            const ret_type = function.returns.values()[0].ty;
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
        args: *const std.StringArrayHashMapUnmanaged(syntax.pure.Tree.Index),

        fn get(scope: *const Scope, name: []const u8) ?syntax.pure.Tree.Index {
            const function = @fieldParentPtr(Scope.Fn, "base", scope);
            const param = function.args.get(name) orelse return null;
            return param;
        }
    };
};

fn lookUpType(ctx: *Context, key: Type.Key) !Type.Index {
    const result = try ctx.types.getOrPutAdapted(ctx.allocator, key, Type.HashContext{ .ctx = ctx });
    if (!result.found_existing) {
        result.value_ptr.* = switch (key) {
            .invalid => .invalid,
            .bool => .bool,
            .unsigned_integer => |unsigned_integer| .{ .unsigned_integer = .{ .bits = unsigned_integer.bits } },
            .pointer_to => |pointee| .{ .pointer_to = pointee },
            .structure => |structure| blk: {
                const struct_index = ctx.structures.items.len;
                const ident = structure.ident(ctx.root) orelse return error.Syntax;
                const name = ctx.root.tokenText(ident);
                try ctx.structures.append(ctx.allocator, .{ .syntax = structure, .name = name });
                break :blk .{ .structure = @enumFromInt(struct_index) };
            },
            .function => |function| blk: {
                const function_index = ctx.functions.items.len;
                const ident = function.ident(ctx.root) orelse return error.Syntax;
                const name = ctx.root.tokenText(ident);
                try ctx.functions.append(ctx.allocator, .{ .syntax = function, .name = name });
                break :blk .{ .function = @enumFromInt(function_index) };
            },
        };
    }
    return @enumFromInt(result.index);
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

            try ctx.addDiagnostic(ctx.root.treeSpan(unary.tree), "unknown binary operator", .{});

            return ctx.lookUpType(.invalid);
        },
    }
}

fn checkFnBody(ctx: *Context, scope: *const Scope, function: Fn.Index) !void {
    const body = ctx.fnPtr(function).syntax.body(ctx.root) orelse return error.Syntax;

    var args: std.StringArrayHashMapUnmanaged(syntax.pure.Tree.Index) = .{};
    defer args.deinit(ctx.allocator);

    const params = ctx.fnPtr(function).syntax.params(ctx.root) orelse return error.Syntax;
    var it = params.params(ctx.root);
    while (it.next(ctx.root)) |param| {
        const name_syntax = param.ident(ctx.root) orelse return error.Syntax;
        const name = ctx.root.tokenText(name_syntax);
        try args.put(ctx.allocator, name, param.tree);
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
                for (returns.values()) |ret| {
                    const expr = exprs.next(ctx.root) orelse return error.Syntax;
                    try checkExpr(ctx, scope, function, expr);
                    const inferred_type = try ctx.analyzeExpr(scope, expr, null);
                    if (inferred_type != ret.ty) {
                        try ctx.addDiagnostic(
                            ctx.root.treeSpan(return_stmt.tree),
                            "return type mismatch: declared {}, inferred {}",
                            .{
                                ctx.fmtType(inferred_type),
                                ctx.fmtType(ret.ty),
                            },
                        );
                    }
                }
                if (exprs.next(ctx.root)) |expr| {
                    try ctx.addDiagnostic(ctx.root.treeSpan(expr.tree()), "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                const cond = if_stmt.cond(ctx.root) orelse return error.Syntax;
                try checkExpr(ctx, scope, function, cond);
                const bool_type = try ctx.lookUpType(.bool);
                const cond_type = try ctx.analyzeExpr(scope, cond, bool_type);
                if (cond_type != bool_type) {
                    try ctx.addDiagnostic(
                        ctx.root.treeSpan(cond.tree()),
                        "expected {}, got {}",
                        .{ ctx.fmtType(bool_type), ctx.fmtType(cond_type) },
                    );
                }
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

const Gen = struct {
    vars: std.AutoHashMapUnmanaged(syntax.pure.Tree.Index, ir.Reg) = .{},
};

fn genBlock(ctx: *Context, gen: *Gen, scope: *const Scope, block: syntax.ast.Stmt.Block, builder: *ir.Builder) !void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        const child_tree = child.asTree() orelse continue;
        const stmt = syntax.ast.Stmt.cast(ctx.root, child_tree) orelse return error.Syntax;
        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = expr_stmt.expr(ctx.root) orelse return error.Syntax;
                _ = try genExpr(ctx, gen, scope, expr, builder);
            },
            .block => |nested_block| {
                return ctx.genBlock(gen, scope, nested_block, builder);
            },
            .@"return" => |return_stmt| {
                var exprs = return_stmt.exprs(ctx.root);
                var regs: std.ArrayListUnmanaged(ir.Reg) = .{};
                defer regs.deinit(ctx.allocator);
                while (exprs.next(ctx.root)) |expr| {
                    const value = try genExpr(ctx, gen, scope, expr, builder);
                    if (value != .reg) {
                        try ctx.addDiagnostic(ctx.root.treeSpan(expr.tree()), "cannot use void value", .{});
                        return;
                    }
                    try regs.append(ctx.allocator, value.reg);
                }
                return builder.buildRet(regs.items);
            },
            .@"if" => |if_stmt| {
                const cond = if_stmt.cond(ctx.root) orelse return error.Syntax;
                const cond_value = try genExpr(ctx, gen, scope, cond, builder);
                const then_block = try builder.addBlock(&.{});
                const cont_block = try builder.addBlock(&.{});
                try builder.buildBranch(cond_value.reg, then_block, cont_block);
                builder.switchToBlock(then_block);
                const if_body = if_stmt.body(ctx.root) orelse return error.Syntax;
                try ctx.genBlock(gen, scope, if_body, builder);
                try builder.buildJump(cont_block);
                builder.switchToBlock(cont_block);
            },
        }
    }
}

const Value = union(enum) {
    invalid,
    void,
    reg: ir.Reg,
};

fn genExpr(ctx: *Context, gen: *Gen, scope: *const Scope, expr: syntax.ast.Expr, builder: *ir.Builder) !Value {
    switch (expr) {
        .unary => |unary| {
            _ = unary;
            return error.UnknownUnaryOperator;
        },
        .binary => |binary_expr| {
            if (binary_expr.plus(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .add);
            if (binary_expr.minus(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .sub);
            if (binary_expr.star(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .mul);
            if (binary_expr.slash(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .div);
            if (binary_expr.percent(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .rem);
            if (binary_expr.lt2(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .shl);
            if (binary_expr.gt2(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .shr);
            if (binary_expr.ampersand(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .band);
            if (binary_expr.pipe(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .bor);
            if (binary_expr.caret(ctx.root) != null) return genArithExpr(ctx, gen, scope, binary_expr, builder, .bxor);
            if (binary_expr.eq2(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .eq);
            if (binary_expr.bangEq(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .neq);
            if (binary_expr.lt(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .lt);
            if (binary_expr.ltEq(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .lte);
            if (binary_expr.gt(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .gt);
            if (binary_expr.gtEq(ctx.root) != null) return genCmpExpr(ctx, gen, scope, binary_expr, builder, .gte);
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
            return genExpr(ctx, gen, scope, inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse return error.Syntax;
            const ident = syntax.ast.Expr.Ident.cast(ctx.root, inner.tree()) orelse return error.CannotCallNonIdentifier;
            const name = ctx.root.tokenText(ident.ident(ctx.root) orelse return error.Syntax);
            const decl_syntax = scope.get(name) orelse return error.UndefinedIdentifier;
            const fn_syntax = syntax.ast.Decl.Fn.cast(ctx.root, decl_syntax) orelse return error.TODO;
            const function_ty = try ctx.lookUpType(.{ .function = fn_syntax });
            const function = ctx.fnPtr(ctx.typePtr(function_ty).function);
            const dname = try builder.allocator.dupe(u8, name);
            var params = try std.ArrayListUnmanaged(ir.Type).initCapacity(builder.allocator, function.params.entries.len);
            defer params.deinit(builder.allocator);
            for (function.params.values()) |param| params.appendAssumeCapacity(try irType(ctx, param.ty));
            var returns = try std.ArrayListUnmanaged(ir.Type).initCapacity(builder.allocator, function.returns.entries.len);
            defer returns.deinit(builder.allocator);
            for (function.returns.values()) |ret| returns.appendAssumeCapacity(try irType(ctx, ret.ty));
            const extern_func = try builder.declareExternFunc(dname, try params.toOwnedSlice(builder.allocator), try returns.toOwnedSlice(builder.allocator));
            var arg_regs = try std.ArrayListUnmanaged(ir.Reg).initCapacity(ctx.allocator, params.items.len);
            defer arg_regs.deinit(ctx.allocator);
            var it = (call.args(ctx.root) orelse return error.Syntax).args(ctx.root);
            while (it.next(ctx.root)) |arg_syntax| {
                const arg_expr = arg_syntax.expr(ctx.root) orelse return error.Syntax;
                const arg_reg = try genExpr(ctx, gen, scope, arg_expr, builder);
                try arg_regs.append(ctx.allocator, arg_reg.reg);
            }
            const return_regs = try builder.buildCall(extern_func, arg_regs.items);
            return switch (return_regs.len) {
                0 => .void,
                1 => .{ .reg = return_regs[0] },
                else => std.debug.panic("TODO: {}", .{return_regs.len}),
            };
        },
        .ident => |ident| {
            const inner = ident.ident(ctx.root) orelse return error.Syntax;
            const text = ctx.root.tokenText(inner);
            const tree = scope.get(text) orelse return error.UndefinedIdentifier;
            if (gen.vars.get(tree)) |reg|
                return .{ .reg = reg };
            return error.TODO;
        },
    }
}

fn genArithExpr(ctx: *Context, gen: *Gen, scope: *const Scope, expr: syntax.ast.Expr.Binary, builder: *ir.Builder, op: ir.ArithOp) !Value {
    const lhs = expr.lhs(ctx.root) orelse return error.Syntax;
    const rhs = expr.rhs(ctx.root) orelse return error.Syntax;
    const lhs_value = try genExpr(ctx, gen, scope, lhs, builder);
    const rhs_value = try genExpr(ctx, gen, scope, rhs, builder);
    if (lhs_value != .reg or rhs_value != .reg) {
        if (lhs_value == .void or rhs_value == .void)
            try ctx.addDiagnostic(ctx.root.treeSpan(expr.tree), "cannot use void value", .{});
        return .invalid;
    }

    return .{ .reg = try builder.buildArith(op, lhs_value.reg, rhs_value.reg) };
}

fn genCmpExpr(ctx: *Context, gen: *Gen, scope: *const Scope, expr: syntax.ast.Expr.Binary, builder: *ir.Builder, op: ir.CmpOp) !Value {
    const lhs = expr.lhs(ctx.root) orelse return error.Syntax;
    const rhs = expr.rhs(ctx.root) orelse return error.Syntax;
    const lhs_value = try genExpr(ctx, gen, scope, lhs, builder);
    const rhs_value = try genExpr(ctx, gen, scope, rhs, builder);
    if (lhs_value != .reg or rhs_value != .reg) {
        if (lhs_value == .void or rhs_value == .void)
            try ctx.addDiagnostic(ctx.root.treeSpan(expr.tree), "cannot use void value", .{});
        return .invalid;
    }

    return .{ .reg = try builder.buildCmp(op, lhs_value.reg, rhs_value.reg) };
}

fn irType(ctx: *Context, type_index: Type.Index) !ir.Type {
    const ty = ctx.typePtr(type_index);
    return switch (ty.*) {
        .invalid => @panic("TODO"),
        .bool => .i64,
        .unsigned_integer => .i64,
        .pointer_to => .ptr,
        .structure => @panic("TODO"),
        .function => @panic("TODO"),
    };
}
