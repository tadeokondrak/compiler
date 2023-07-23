const Sema = @This();

const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");
const LineIndex = @import("LineIndex.zig");
const ast = @import("ast");

gpa: std.mem.Allocator,
ast: ast.File,
type_pool: std.AutoArrayHashMapUnmanaged(void, void) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
scope_pool: std.AutoArrayHashMapUnmanaged(void, void) = .{},
scopes: std.ArrayListUnmanaged(Scope) = .{},
structures: std.ArrayListUnmanaged(Struct) = .{},
functions: std.ArrayListUnmanaged(Fn) = .{},
diagnostics: std.MultiArrayList(Diagnostic) = .{},

pub const Type = union(enum) {
    invalid,
    bool,
    generic,
    unsigned_integer: struct { bits: u32 },
    pointer: Type.Index,
    structure: Struct.Index,
    function: Fn.Index,

    pub const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const Key = union(enum) {
        invalid,
        bool,
        generic,
        unsigned_integer: struct { bits: u32 },
        pointer: Type.Index,
        structure: ast.Ptr(ast.DeclStruct),
        function: ast.Ptr(ast.DeclFn),
    };

    pub fn get(ctx: *Sema, key: Type.Key) error{OutOfMemory}!Type.Index {
        const result = try ctx.type_pool.getOrPutAdapted(
            ctx.gpa,
            key,
            Type.HashContext{ .ctx = ctx },
        );
        if (!result.found_existing) {
            std.debug.assert(result.index == ctx.types.items.len);
            try ctx.types.append(ctx.gpa, switch (key) {
                .invalid => .invalid,
                .bool => .bool,
                .generic => .generic,
                .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
                .pointer => |pointee| .{ .pointer = pointee },
                .structure => |structure_ptr| blk: {
                    const structure = try structure_ptr.deref(ctx.ast.tree);

                    const struct_index = ctx.structures.items.len;
                    const ident = try structure.identToken() orelse
                        return typeTodo(ctx, structure.span(), @src());

                    try ctx.structures.append(ctx.gpa, .{ .syntax = structure.ptr(), .name = ident.text() });
                    break :blk .{ .structure = @enumFromInt(struct_index) };
                },
                .function => |function_ptr| blk: {
                    const function = try function_ptr.deref(ctx.ast.tree);

                    const function_index = ctx.functions.items.len;
                    const ident = try function.identToken() orelse
                        return typeTodo(ctx, function.span(), @src());

                    try ctx.functions.append(ctx.gpa, .{ .syntax = function.ptr(), .name = ident.text() });
                    break :blk .{ .function = @enumFromInt(function_index) };
                },
            });
        }
        return @enumFromInt(result.index);
    }

    fn toKey(ctx: *Sema, ty: Type) Key {
        return switch (ty) {
            .invalid => .invalid,
            .bool => .bool,
            .generic => .generic,
            .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
            .pointer => |pointee| .{ .pointer = pointee },
            .structure => |structure| .{ .structure = structPtr(ctx, structure).syntax },
            .function => |function| .{ .function = fnPtr(ctx, function).syntax },
        };
    }

    const HashContext = struct {
        ctx: *Sema,

        pub fn hash(_: @This(), key: Key) u32 {
            var hasher = std.hash.Wyhash.init(0);
            std.hash.autoHash(&hasher, key);
            return @truncate(hasher.final());
        }

        pub fn eql(self: @This(), key: Key, _: void, b_index: usize) bool {
            const other_key = toKey(self.ctx, self.ctx.types.items[b_index]);
            return std.meta.eql(key, other_key);
        }
    };
};

const Struct = struct {
    analysis: enum { unanalyzed, analyzing, analyzed } = .unanalyzed,
    syntax: ast.Ptr(ast.DeclStruct),
    name: []const u8,
    fields: std.StringArrayHashMapUnmanaged(Type.Index) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

const Fn = struct {
    analysis: enum { unanalyzed, analyzing, analyzed } = .unanalyzed,
    syntax: ast.Ptr(ast.DeclFn),
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(Type.Index) = .{},
    returns: std.StringArrayHashMapUnmanaged(Type.Index) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

pub const Diagnostic = struct {
    span: syntax.pure.Span,
    message: []const u8,
};

pub const Scope = struct {
    parent: Index,
    data: Data,

    pub const Key = union(enum) {
        builtin,
        file: ast.Ptr(ast.File),
        generics: ast.Ptr(ast.Generics),
        params: ast.Ptr(ast.Params),
    };

    pub const Data = union(enum) {
        builtin,
        file: ast.Ptr(ast.File),
        generics: ast.Ptr(ast.Generics),
        params: ast.Ptr(ast.Params),
    };

    pub const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const LookupResult = union(enum) {
        decl: ast.Ptr(ast.Decl),
        fn_param: ast.Ptr(ast.Param),
        generic: ast.Ptr(ast.Generic),
        true,
        false,
        null,
    };

    pub fn toKey(ctx: *Sema, scope: Scope) Key {
        _ = ctx;
        return switch (scope.data) {
            .builtin => .builtin,
            .file => |file| .{ .file = file },
            .generics => |generics| .{ .generics = generics },
            .params => |params| .{ .params = params },
        };
    }

    pub fn get(ctx: *Sema, key: Scope.Key) error{OutOfMemory}!Scope.Index {
        const result = try ctx.scope_pool.getOrPutAdapted(
            ctx.gpa,
            key,
            Scope.HashContext{ .ctx = ctx },
        );
        if (!result.found_existing) {
            std.debug.assert(result.index == ctx.scopes.items.len);
            const scope = try ctx.scopes.addOne(ctx.gpa);
            switch (key) {
                .builtin => scope.* = .{ .parent = .invalid, .data = .builtin },
                .file => |file_ptr| {
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .file = file_ptr },
                    };
                    scope.parent = try get(ctx, .builtin);
                },
                .generics => |generics_ptr| {
                    const generics = try generics_ptr.deref(ctx.ast.tree);
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .generics = generics_ptr },
                    };
                    scope.parent = if (ast.DeclFn.cast(generics.tree.parent.?)) |function|
                        try find(ctx, function.tree.parent.?)
                    else if (ast.DeclStruct.cast(generics.tree.parent.?)) |structure|
                        try find(ctx, structure.tree.parent.?)
                    else
                        try find(ctx, generics.tree.parent.?);
                },
                .params => |params_ptr| {
                    const params = try params_ptr.deref(ctx.ast.tree);
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .params = params_ptr },
                    };
                    const function = ast.DeclFn.cast(params.tree.parent.?).?;
                    scope.parent = if (try function.genericsNode()) |generics|
                        try get(ctx, .{ .generics = generics.ptr() })
                    else
                        try find(ctx, function.tree.parent.?);
                },
            }
        }
        return @enumFromInt(result.index);
    }

    pub fn find(ctx: *Sema, node_arg: *const syntax.Tree) error{OutOfMemory}!Scope.Index {
        var node: ?*const syntax.Tree = node_arg;
        while (node) |current_node| : (node = current_node.parent) {
            switch (current_node.tag) {
                .file => {
                    const file = ast.File.cast(current_node).?;
                    return Scope.get(ctx, .{ .file = file.ptr() });
                },
                .decl_fn => {
                    const fn_decl = ast.DeclFn.cast(current_node).?;
                    if (try fn_decl.paramsNode()) |params|
                        return Scope.get(ctx, .{ .params = params.ptr() });
                },
                .decl_struct => {
                    const struct_decl = ast.DeclStruct.cast(current_node).?;
                    if (try struct_decl.genericsNode()) |generics|
                        return Scope.get(ctx, .{ .generics = generics.ptr() });
                },
                .stmt_let => {
                    // TODO
                },
                else => {},
            }
        }
        @panic("TODO");
    }

    fn lookUp(
        ctx: *Sema,
        scope_index: Index,
        name: []const u8,
    ) !?LookupResult {
        const scope = ctx.scopePtr(scope_index);

        switch (scope.data) {
            .builtin => {
                const map = std.ComptimeStringMap(LookupResult, .{
                    .{ "null", .null },
                    .{ "true", .true },
                    .{ "false", .false },
                });
                return map.get(name);
            },
            .file => |file_ptr| {
                const file = try file_ptr.deref(ctx.ast.tree);
                var decls = file.declNodes();
                while (try decls.next()) |decl| {
                    const decl_ident = switch (decl) {
                        inline else => |specific| try specific.identToken() orelse continue,
                    };
                    if (std.mem.eql(u8, name, decl_ident.text()))
                        return .{ .decl = decl.ptr() };
                }
            },
            .generics => |generics_ptr| {
                const generics = try generics_ptr.deref(ctx.ast.tree);
                var generics_iter = generics.genericNodes();
                while (try generics_iter.next()) |generic| {
                    const generic_ident = try generic.identToken() orelse continue;
                    if (std.mem.eql(u8, name, generic_ident.text()))
                        return .{ .generic = generic.ptr() };
                }
            },
            .params => |params_ptr| {
                const params = try params_ptr.deref(ctx.ast.tree);
                var params_iter = params.paramNodes();
                while (try params_iter.next()) |param| {
                    const param_ident = try param.identToken() orelse continue;
                    if (std.mem.eql(u8, name, param_ident.text()))
                        return .{ .fn_param = param.ptr() };
                }
            },
        }

        return if (scope.parent != .invalid)
            Scope.lookUp(ctx, scope.parent, name)
        else
            null;
    }

    const HashContext = struct {
        ctx: *Sema,

        pub fn hash(_: @This(), key: Key) u32 {
            var hasher = std.hash.Wyhash.init(0);
            std.hash.autoHash(&hasher, key);
            return @truncate(hasher.final());
        }

        pub fn eql(self: @This(), key: Key, _: void, b_index: usize) bool {
            const other_key = toKey(self.ctx, self.ctx.scopes.items[b_index]);
            return std.meta.eql(key, other_key);
        }
    };
};

pub fn typePtr(ctx: *Sema, i: Type.Index) *Type {
    return &ctx.types.items[@intFromEnum(i)];
}

pub fn scopePtr(ctx: *Sema, i: Scope.Index) *Scope {
    return &ctx.scopes.items[@intFromEnum(i)];
}

pub fn structPtr(ctx: *Sema, i: Struct.Index) *Struct {
    return &ctx.structures.items[@intFromEnum(i)];
}

pub fn fnPtr(ctx: *Sema, i: Fn.Index) *Fn {
    return &ctx.functions.items[@intFromEnum(i)];
}

fn err(
    ctx: *Sema,
    span: syntax.pure.Span,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!void {
    return ctx.diagnostics.append(ctx.gpa, .{
        .span = span,
        .message = try std.fmt.allocPrint(ctx.gpa, fmt, args),
    });
}

fn todo(
    ctx: *Sema,
    span: syntax.pure.Span,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!void {
    return err(
        ctx,
        span,
        "TODO in {s} at {s}:{}:{}",
        .{ src.fn_name, src.file, src.line, src.column },
    );
}

fn typeErr(
    ctx: *Sema,
    span: syntax.pure.Span,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!Type.Index {
    try err(ctx, span, fmt, args);
    return Type.get(ctx, .invalid);
}

fn typeTodo(
    ctx: *Sema,
    span: syntax.pure.Span,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!Type.Index {
    try todo(ctx, span, src);
    return Type.get(ctx, .invalid);
}

const FormatFnArgs = struct { ctx: *Sema, function: Fn.Index };

fn formatFn(
    args: FormatFnArgs,
    comptime _: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
    const function = fnPtr(args.ctx, args.function);
    try writer.print("fn {s}(", .{function.name});
    for (function.params.keys(), function.params.values(), 0..) |key, value, i| {
        if (i > 0) try writer.print(", ", .{});
        try writer.print("{s}: {}", .{ key, fmtType(args.ctx, value) });
    }
    try writer.print(") (", .{});
    for (function.returns.keys(), function.returns.values(), 0..) |key, value, i| {
        if (i > 0) try writer.print(", ", .{});
        try writer.print("{s}: {}", .{ key, fmtType(args.ctx, value) });
    }
    try writer.print(")", .{});
}

pub fn fmtFn(ctx: *Sema, function: Fn.Index) std.fmt.Formatter(formatFn) {
    return .{ .data = .{ .ctx = ctx, .function = function } };
}

const FormatStructArgs = struct { ctx: *Sema, structure: Struct.Index };

fn formatStruct(
    args: FormatStructArgs,
    comptime fmt: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
    const structure = structPtr(args.ctx, args.structure);
    if (std.mem.eql(u8, fmt, "#")) {
        try writer.print("struct {s}", .{structure.name});
        try writer.print(" {{", .{});
        for (structure.fields.keys(), structure.fields.values(), 0..) |key, value, i| {
            if (i > 0) try writer.print(",", .{});
            try writer.print(" {s}: {}", .{ key, fmtType(args.ctx, value) });
        }
        try writer.print(" }}", .{});
    } else {
        try writer.writeAll(structure.name);
    }
}

pub fn fmtStruct(ctx: *Sema, structure: Struct.Index) std.fmt.Formatter(formatStruct) {
    return .{ .data = .{ .ctx = ctx, .structure = structure } };
}

const FormatScopeArgs = struct { ctx: *Sema, scope: Scope.Index };

fn formatScope(
    args: FormatScopeArgs,
    comptime _: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
    const scope = scopePtr(args.ctx, args.scope);
    if (scope.parent != .invalid)
        try writer.print("{} -> ", .{fmtScope(args.ctx, scope.parent)});
    try writer.writeAll(@tagName(scope.data));
}

pub fn fmtScope(ctx: *Sema, scope: Scope.Index) std.fmt.Formatter(formatScope) {
    return .{ .data = .{ .ctx = ctx, .scope = scope } };
}

const FormatTypeArgs = struct { ctx: *Sema, ty: Type.Index };

fn formatType(
    args: FormatTypeArgs,
    comptime fmt: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
    return switch (typePtr(args.ctx, args.ty).*) {
        .invalid => writer.print("invalid", .{}),
        .bool => writer.print("bool", .{}),
        .generic => writer.print("?", .{}),
        .unsigned_integer => |unsigned_integer| writer.print("u{}", .{unsigned_integer.bits}),
        .pointer => |pointee| writer.print("*{}", .{fmtType(args.ctx, pointee)}),
        .structure => |structure| fmtStruct(args.ctx, structure).format(fmt, .{}, writer),
        .function => |function| fmtFn(args.ctx, function).format(fmt, .{}, writer),
    };
}

pub fn fmtType(ctx: *Sema, ty: Type.Index) std.fmt.Formatter(formatType) {
    return .{ .data = .{ .ctx = ctx, .ty = ty } };
}

pub fn printDiagnostics(
    ctx: *Sema,
    src: []const u8,
    writer: anytype,
) (@TypeOf(writer).Error || error{OutOfMemory})!bool {
    if (ctx.diagnostics.len == 0)
        return false;
    const line_index = try LineIndex.make(ctx.gpa, src);
    defer line_index.deinit(ctx.gpa);
    for (ctx.diagnostics.items(.span), ctx.diagnostics.items(.message)) |span, message| {
        const start = line_index.translate(span.start.offset);
        const end = line_index.translate(span.end.offset);
        const len = if (start.line != end.line) 1 else end.col - start.col;
        try writer.print("<input>:{}:{}: {s}\n", .{ start.line + 1, start.col + 1, message });
        const line_start = if (start.line == 0) 0 else line_index.newlines[start.line - 1] + 1;
        const line_end = if (end.line == line_index.newlines.len) src.len else line_index.newlines[end.line];
        const line = src[line_start..line_end];
        for (line) |c|
            try writer.writeByte(c);
        try writer.writeByte('\n');
        for (0..start.col) |_|
            try writer.writeByte(' ');
        for (0..len) |_|
            try writer.writeByte('^');
        try writer.writeByte('\n');
    }
    return true;
}

pub fn deinit(ctx: *Sema) void {
    for (ctx.diagnostics.items(.message)) |message|
        ctx.gpa.free(message);
    ctx.diagnostics.deinit(ctx.gpa);
    for (ctx.functions.items) |*function| {
        function.params.deinit(ctx.gpa);
        function.returns.deinit(ctx.gpa);
    }
    for (ctx.structures.items) |*structure|
        structure.fields.deinit(ctx.gpa);
    ctx.structures.deinit(ctx.gpa);
    ctx.functions.deinit(ctx.gpa);
    ctx.scope_pool.deinit(ctx.gpa);
    ctx.scopes.deinit(ctx.gpa);
    ctx.type_pool.deinit(ctx.gpa);
    ctx.types.deinit(ctx.gpa);
}

pub fn dump(ctx: *Sema, writer: anytype) (@TypeOf(writer).Error || error{OutOfMemory})!void {
    for (0..ctx.type_pool.entries.len) |i|
        try writer.print("Type {}: {#}\n", .{ i, fmtType(ctx, @enumFromInt(i)) });
    for (0..ctx.scope_pool.entries.len) |i|
        try writer.print("Scope {}: {}\n", .{ i, fmtScope(ctx, @enumFromInt(i)) });
}

pub fn analyzeDecl(ctx: *Sema, decl: ast.Decl) error{OutOfMemory}!void {
    switch (decl) {
        .structure => |struct_syntax| {
            var type_index = try Type.get(ctx, .{ .structure = struct_syntax.ptr() });
            var struct_index = typePtr(ctx, type_index).structure;
            var structure = structPtr(ctx, struct_index);
            try analyzeStruct(ctx, structure);
        },
        .function => |function_syntax| {
            var type_index = try Type.get(ctx, .{ .function = function_syntax.ptr() });
            var function_index = typePtr(ctx, type_index).function;
            var function = fnPtr(ctx, function_index);
            try analyzeFn(ctx, function);
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExprNode() orelse
                return err(ctx, constant_syntax.span(), "constant without type", .{});

            const ty = try analyzeTypeExpr(ctx, type_expr);
            const expr = try constant_syntax.exprNode() orelse
                return err(ctx, constant_syntax.span(), "constant without initializer", .{});

            const expr_ty = try analyzeExpr(ctx, expr, ty);
            if (ty != expr_ty) {
                try err(ctx, expr.span(), "expected {}, got {}", .{
                    fmtType(ctx, ty),
                    fmtType(ctx, expr_ty),
                });
            }
        },
    }
}

fn analyzeFn(ctx: *Sema, function: *Fn) !void {
    if (function.analysis == .analyzed or function.analysis == .analyzing) return;

    function.analysis = .analyzing;

    const function_syntax = try function.syntax.deref(ctx.ast.tree);

    params: {
        const params = try function_syntax.paramsNode() orelse
            break :params;

        var it = params.paramNodes();
        while (try it.next()) |param| {
            const name_syntax = try param.identToken() orelse
                return err(ctx, param.span(), "function parameter without name", .{});

            const type_syntax = try param.typeExprNode() orelse
                return err(ctx, param.span(), "function parameter without type", .{});

            const ty = try analyzeTypeExpr(ctx, type_syntax);
            try function.params.put(ctx.gpa, name_syntax.text(), ty);
        }
    }

    returns: {
        const returns = try function_syntax.returnsNode() orelse
            break :returns;

        var it = returns.paramNodes();
        while (try it.next()) |param| {
            const name_syntax = try param.identToken() orelse
                return err(ctx, param.span(), "function return without name", .{});

            const type_syntax = try param.typeExprNode() orelse
                return err(ctx, param.span(), "function return without type", .{});

            const ty = try analyzeTypeExpr(ctx, type_syntax);
            try function.returns.put(ctx.gpa, name_syntax.text(), ty);
        }
    }

    const body = try function_syntax.stmtBlockNode() orelse
        return todo(ctx, function.syntax.span, @src());

    try checkBlock(ctx, function, body);

    function.analysis = .analyzed;
}

fn analyzeStruct(ctx: *Sema, structure: *Struct) !void {
    if (structure.analysis == .analyzed or structure.analysis == .analyzing) return;

    structure.analysis = .analyzing;

    std.debug.assert(structure.fields.entries.len == 0);
    const function_syntax = try structure.syntax.deref(ctx.ast.tree);
    var it = function_syntax.fieldNodes();
    while (try it.next()) |field| {
        const name_syntax = try field.identToken() orelse
            return err(ctx, field.span(), "struct field without name", .{});

        const type_syntax = try field.typeExprNode() orelse
            return err(ctx, field.span(), "struct field without type", .{});

        const ty = try analyzeTypeExpr(ctx, type_syntax);
        try structure.fields.put(ctx.gpa, name_syntax.text(), ty);
    }

    structure.analysis = .analyzed;
}

// may return a type other than/incompatible with expected_type
pub fn analyzeExpr(
    ctx: *Sema,
    expr: ast.Expr,
    maybe_expected_type: ?Type.Index,
) error{OutOfMemory}!Type.Index {
    switch (expr) {
        .paren => |paren_expr| {
            const sub_expr = try paren_expr.exprNode() orelse
                return typeTodo(ctx, paren_expr.span(), @src());
            return analyzeExpr(ctx, sub_expr, maybe_expected_type);
        },
        .literal => |literal_expr| {
            if (try literal_expr.numberToken()) |_| {
                if (maybe_expected_type) |expected_type| {
                    if (typePtr(ctx, expected_type).* == .unsigned_integer)
                        return expected_type;

                    try err(
                        ctx,
                        expr.span(),
                        "expected {}, got untyped number",
                        .{fmtType(ctx, expected_type)},
                    );
                } else {
                    return Type.get(ctx, .{ .unsigned_integer = .{ .bits = 32 } });
                }
            }

            return typeTodo(ctx, literal_expr.span(), @src());
        },
        .ident => |ident_expr| {
            const ident = try ident_expr.identToken() orelse
                return typeTodo(ctx, ident_expr.span(), @src());

            const scope = try Scope.find(ctx, ident_expr.tree);
            const lookup_result = try Scope.lookUp(ctx, scope, ident.text()) orelse
                return typeErr(ctx, ident_expr.span(), "undefined identifier: {s}", .{ident.text()});

            switch (lookup_result) {
                .decl => |decl| {
                    return typeOfDecl(ctx, try decl.deref(ctx.ast.tree));
                },
                .fn_param => |fn_param_ptr| {
                    const fn_param = try fn_param_ptr.deref(ctx.ast.tree);

                    const type_expr = try fn_param.typeExprNode() orelse
                        return typeTodo(ctx, ident_expr.span(), @src());

                    return try analyzeTypeExpr(ctx, type_expr);
                },
                .true, .false => return Type.get(ctx, .bool),
                .null => {
                    if (maybe_expected_type) |expected_type| {
                        if (typePtr(ctx, expected_type).* == .pointer)
                            return expected_type;

                        try err(
                            ctx,
                            expr.span(),
                            "expected {}, got untyped null",
                            .{fmtType(ctx, expected_type)},
                        );
                    }

                    return typeTodo(ctx, ident_expr.span(), @src());
                },
                .generic => |generic| return typeTodo(ctx, generic.span, @src()),
            }
        },
        .unary => |unary_expr| {
            return typeTodo(ctx, unary_expr.span(), @src());
        },
        .binary => |binary_expr| {
            const lhs_expr = try binary_expr.lhsNode() orelse
                return typeErr(ctx, binary_expr.span(), "binary expression missing left-hand side", .{});

            const rhs_expr = try binary_expr.rhsNode() orelse
                return typeErr(ctx, binary_expr.span(), "binary expression missing right-hand side", .{});

            const lhs_type = try analyzeExpr(ctx, lhs_expr, null);
            const rhs_type = try analyzeExpr(ctx, rhs_expr, null);

            if (try binary_expr.plusToken() != null or
                try binary_expr.minusToken() != null or
                try binary_expr.starToken() != null or
                try binary_expr.slashToken() != null or
                try binary_expr.percentToken() != null or
                try binary_expr.lt2Token() != null or
                try binary_expr.gt2Token() != null or
                try binary_expr.ampersandToken() != null or
                try binary_expr.pipeToken() != null or
                try binary_expr.caretToken() != null)
            {
                if (lhs_type == rhs_type)
                    return lhs_type;
                try err(
                    ctx,
                    binary_expr.span(),
                    "arithmetic operator type mismatch: lhs {}, rhs {}",
                    .{ fmtType(ctx, lhs_type), fmtType(ctx, rhs_type) },
                );
                return Type.get(ctx, .invalid);
            }

            if (try binary_expr.eq2Token() != null or
                try binary_expr.bangEqToken() != null or
                try binary_expr.ltToken() != null or
                try binary_expr.ltEqToken() != null or
                try binary_expr.gtToken() != null or
                try binary_expr.gtEqToken() != null)
            {
                if (lhs_type == rhs_type)
                    return Type.get(ctx, .bool);
                try err(
                    ctx,
                    binary_expr.span(),
                    "comparison operator type mismatch: lhs {}, rhs {}",
                    .{ fmtType(ctx, lhs_type), fmtType(ctx, rhs_type) },
                );
                return Type.get(ctx, .invalid);
            }

            return typeTodo(ctx, binary_expr.span(), @src());
        },
        .call => |call_expr| {
            const fn_expr = try call_expr.exprNode() orelse
                return typeTodo(ctx, call_expr.span(), @src());

            const fn_type_index = try analyzeExpr(ctx, fn_expr, null);
            const fn_type = typePtr(ctx, fn_type_index);
            if (fn_type.* != .function) {
                return typeErr(
                    ctx,
                    call_expr.span(),
                    "can't call non-function {}",
                    .{fmtType(ctx, fn_type_index)},
                );
            }

            const function = fnPtr(ctx, fn_type.function);
            try analyzeFn(ctx, function);

            const params = function.params;
            const args_wrapper = try call_expr.argumentsNode() orelse
                return typeTodo(ctx, call_expr.span(), @src());

            var args = args_wrapper.argumentNodes();
            for (params.values()) |param_ty| {
                const arg = try args.next() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_expr = try arg.exprNode() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_type = try analyzeExpr(ctx, arg_expr, null);
                if (arg_type != param_ty)
                    return typeTodo(ctx, call_expr.span(), @src());
            }

            if (try args.next()) |_|
                return typeTodo(ctx, call_expr.span(), @src());

            if (function.returns.values().len != 1)
                return typeTodo(ctx, call_expr.span(), @src());

            const ret_type = function.returns.values()[0];
            return ret_type;
        },
    }
}

pub fn analyzeTypeExpr(ctx: *Sema, type_expr: ast.TypeExpr) error{OutOfMemory}!Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = try ident.identToken() orelse
                return typeTodo(ctx, ident.span(), @src());

            const ident_text = ident_token.text();
            if (ident_text.len > 0 and ident_text[0] == 'u') {
                if (std.fmt.parseInt(u32, ident_text[1..], 10)) |bits| {
                    return Type.get(ctx, .{ .unsigned_integer = .{ .bits = bits } });
                } else |e| switch (e) {
                    error.Overflow => return typeTodo(ctx, ident.span(), @src()),
                    error.InvalidCharacter => {},
                }
            }

            const scope = try Scope.find(ctx, ident.tree);

            const lookup_result = try Scope.lookUp(ctx, scope, ident_text) orelse
                return typeErr(ctx, ident.span(), "undefined identifier {s}", .{ident_text});

            switch (lookup_result) {
                .decl => |decl_ptr| {
                    const decl = try decl_ptr.deref(ctx.ast.tree);
                    switch (decl) {
                        .structure => |structure| {
                            return Type.get(ctx, .{ .structure = structure.ptr() });
                        },
                        .function => return typeTodo(ctx, ident.span(), @src()),
                        .constant => return typeTodo(ctx, ident.span(), @src()),
                    }
                },
                .generic => return Type.get(ctx, .generic),
                else => return typeTodo(ctx, ident.span(), @src()),
            }
        },
        .unary => |unary| {
            const operand_type_expr = try unary.typeExprNode() orelse
                return typeErr(ctx, unary.span(), "operator missing operand", .{});

            const operand_type_index = try analyzeTypeExpr(ctx, operand_type_expr);

            if (try unary.starToken() != null)
                return Type.get(ctx, .{ .pointer = operand_type_index });

            try err(ctx, unary.span(), "unknown binary operator", .{});

            return Type.get(ctx, .invalid);
        },
    }
}

fn typeOfDecl(
    ctx: *Sema,
    decl: ast.Decl,
) error{OutOfMemory}!Type.Index {
    switch (decl) {
        .structure => |struct_syntax| {
            return Type.get(ctx, .{ .structure = struct_syntax.ptr() });
        },
        .function => |function_syntax| {
            return Type.get(ctx, .{ .function = function_syntax.ptr() });
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExprNode() orelse
                return typeErr(ctx, constant_syntax.span(), "constant missing type", .{});

            return try analyzeTypeExpr(ctx, type_expr);
        },
    }
}

fn checkBlock(
    ctx: *Sema,
    function: *Fn,
    body: ast.StmtBlock,
) error{OutOfMemory}!void {
    var iter = body.stmtNodes();
    while (try iter.next()) |stmt| {
        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = try expr_stmt.exprNode() orelse
                    return todo(ctx, function.syntax.span, @src());

                try checkExpr(ctx, function, expr, null);
            },
            .block => |block_stmt| {
                try checkBlock(ctx, function, block_stmt);
            },
            .@"return" => |return_stmt| {
                var exprs = return_stmt.exprNodes();
                for (function.returns.values()) |ret_ty| {
                    const expr = try exprs.next() orelse
                        return todo(ctx, function.syntax.span, @src());
                    try checkExpr(ctx, function, expr, ret_ty);
                }
                if (try exprs.next()) |expr| {
                    try err(ctx, expr.span(), "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                if (try if_stmt.exprNode()) |if_cond|
                    try checkExpr(ctx, function, if_cond, try Type.get(ctx, .bool))
                else
                    return err(ctx, if_stmt.span(), "if statement missing condition", .{});

                if (try if_stmt.thenNode()) |if_body|
                    try checkBlock(ctx, function, if_body)
                else
                    return err(ctx, if_stmt.span(), "if statement missing body", .{});
            },
            .loop => |loop_stmt| {
                const loop_body = try loop_stmt.bodyNode() orelse
                    return err(ctx, loop_stmt.span(), "loop missing body", .{});

                try checkBlock(ctx, function, loop_body);
            },
            .@"while" => |while_stmt| {
                if (try while_stmt.exprNode()) |while_cond|
                    try checkExpr(ctx, function, while_cond, try Type.get(ctx, .bool))
                else
                    return err(ctx, while_stmt.span(), "while statement missing condition", .{});

                if (try while_stmt.bodyNode()) |while_body|
                    try checkBlock(ctx, function, while_body)
                else
                    return err(ctx, while_stmt.span(), "while statement missing body", .{});
            },
            .let => |let_stmt| {
                if (try let_stmt.typeExprNode()) |type_expr| {
                    _ = type_expr;
                } else {}

                // TODO
            },
        }
    }
}

fn checkExpr(
    ctx: *Sema,
    function: *Fn,
    expr: ast.Expr,
    maybe_expected_type: ?Type.Index,
) error{OutOfMemory}!void {
    _ = function;
    const ty = try analyzeExpr(ctx, expr, maybe_expected_type);
    if (maybe_expected_type) |expected_type| {
        if (ty != expected_type) {
            try err(
                ctx,
                expr.span(),
                "expected {}, got {}",
                .{ fmtType(ctx, expected_type), fmtType(ctx, ty) },
            );
        }
    }
}
