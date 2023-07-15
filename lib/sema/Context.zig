const Context = @This();

const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");
const LineIndex = @import("LineIndex.zig");

gpa: std.mem.Allocator,
ast: syntax.ast.File,
type_pool: std.AutoArrayHashMapUnmanaged(void, void) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
scope_pool: std.AutoArrayHashMapUnmanaged(void, void) = .{},
scopes: std.ArrayListUnmanaged(Scope) = .{},
structures: std.ArrayListUnmanaged(Struct) = .{},
functions: std.ArrayListUnmanaged(Fn) = .{},
diagnostics: std.MultiArrayList(Diagnostic) = .{},

const Type = union(enum) {
    invalid,
    bool,
    unsigned_integer: struct { bits: u32 },
    pointer: Type.Index,
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
        pointer: Type.Index,
        structure: syntax.ast.Ptr(syntax.ast.Decl.Struct),
        function: syntax.ast.Ptr(syntax.ast.Decl.Fn),
    };

    pub fn get(ctx: *Context, key: Type.Key) error{OutOfMemory}!Type.Index {
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
                .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
                .pointer => |pointee| .{ .pointer = pointee },
                .structure => |structure_ptr| blk: {
                    const structure = try structure_ptr.deref(ctx.ast.tree);

                    const struct_index = ctx.structures.items.len;
                    const ident = try structure.ident() orelse
                        return typeTodo(ctx, structure.span(), @src());

                    try ctx.structures.append(ctx.gpa, .{ .syntax = structure, .name = ident.text() });
                    break :blk .{ .structure = @enumFromInt(struct_index) };
                },
                .function => |function_ptr| blk: {
                    const function = try function_ptr.deref(ctx.ast.tree);

                    const function_index = ctx.functions.items.len;
                    const ident = try function.ident() orelse
                        return typeTodo(ctx, function.span(), @src());

                    try ctx.functions.append(ctx.gpa, .{ .syntax = function, .name = ident.text() });
                    break :blk .{ .function = @enumFromInt(function_index) };
                },
            });
        }
        return @enumFromInt(result.index);
    }

    fn toKey(ctx: *Context, ty: Type) Key {
        return switch (ty) {
            .invalid => .invalid,
            .bool => .bool,
            .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
            .pointer => |pointee| .{ .pointer = pointee },
            .structure => |structure| .{ .structure = structPtr(ctx, structure).syntax.ptr() },
            .function => |function| .{ .function = fnPtr(ctx, function).syntax.ptr() },
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
            const other_key = toKey(self.ctx, self.ctx.types.items[b_index]);
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

pub const Diagnostic = struct {
    span: syntax.pure.Span,
    message: []const u8,
};

pub const Scope = struct {
    parent: Index,
    data: Data,

    pub const Key = union(enum) {
        builtin,
        file: syntax.ast.Ptr(syntax.ast.File),
        generics: syntax.ast.Ptr(syntax.ast.Generics),
        params: syntax.ast.Ptr(syntax.ast.Decl.Fn.Params),
    };

    pub const Data = union(enum) {
        builtin,
        file: syntax.ast.File,
        generics: syntax.ast.Generics,
        params: syntax.ast.Decl.Fn.Params,
    };

    pub const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };

    const LookupResult = union(enum) {
        decl: syntax.ast.Ptr(syntax.ast.Decl),
        fn_param: syntax.ast.Ptr(syntax.ast.Decl.Fn.Param),
        generic: syntax.ast.Ptr(syntax.ast.Generic),
        true,
        false,
        null,
    };

    pub fn toKey(ctx: *Context, scope: Scope) Key {
        _ = ctx;
        return switch (scope.data) {
            .builtin => .builtin,
            .file => |file| .{ .file = file.ptr() },
            .generics => |generics| .{ .generics = generics.ptr() },
            .params => |params| .{ .params = params.ptr() },
        };
    }

    pub fn get(ctx: *Context, key: Scope.Key) error{OutOfMemory}!Scope.Index {
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
                .file => |file| {
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .file = try file.deref(ctx.ast.tree) },
                    };
                    scope.parent = try get(ctx, .builtin);
                },
                .generics => |generics_ptr| {
                    const generics = try generics_ptr.deref(ctx.ast.tree);
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .generics = generics },
                    };
                    scope.parent = if (syntax.ast.Decl.Fn.cast(generics.tree.parent.?)) |function|
                        try find(ctx, function.tree.parent.?)
                    else
                        try find(ctx, generics.tree.parent.?);
                },
                .params => |params_ptr| {
                    const params = try params_ptr.deref(ctx.ast.tree);
                    scope.* = .{
                        .parent = .invalid,
                        .data = .{ .params = params },
                    };
                    const function = syntax.ast.Decl.Fn.cast(params.tree.parent.?).?;
                    scope.parent = if (try function.generics()) |generics|
                        try get(ctx, .{ .generics = generics.ptr() })
                    else
                        try find(ctx, function.tree.parent.?);
                },
            }
        }
        return @enumFromInt(result.index);
    }

    pub fn find(ctx: *Context, node_arg: *syntax.Tree) error{OutOfMemory}!Scope.Index {
        var node: ?*syntax.Tree = node_arg;
        while (node) |current_node| : (node = current_node.parent) {
            switch (current_node.tag) {
                .file => {
                    const file = syntax.ast.File.cast(current_node).?;
                    return Scope.get(ctx, .{ .file = file.ptr() });
                },
                .decl_fn => {
                    const fn_decl = syntax.ast.Decl.Fn.cast(current_node).?;
                    if (try fn_decl.params()) |params|
                        return Scope.get(ctx, .{ .params = params.ptr() });
                },
                .invalid,
                .decl_const,
                .decl_struct,
                .expr_unary,
                .expr_binary,
                .expr_ident,
                .expr_literal,
                .expr_paren,
                .expr_call,
                .expr_index,
                .stmt_block,
                .stmt_expr,
                .stmt_return,
                .stmt_if,
                .stmt_loop,
                .stmt_while,
                .stmt_break,
                .stmt_continue,
                .type_expr_unary,
                .type_expr_ident,
                .fn_params,
                .fn_param,
                .fn_returns,
                .fn_return,
                .call_args,
                .call_arg,
                .struct_field,
                .generics,
                .generic,
                => {},
            }
        }
        @panic("TODO");
    }

    fn lookUp(
        ctx: *Context,
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
            .file => |file| {
                var decls = try file.iter();
                while (decls.next()) |decl| {
                    const decl_ident = try decl.ident() orelse continue;
                    if (std.mem.eql(u8, name, decl_ident.text()))
                        return .{ .decl = decl.ptr() };
                }
            },
            .generics => |generics| {
                var generics_iter = try generics.iter();
                while (generics_iter.next()) |generic| {
                    const generic_ident = try generic.ident() orelse continue;
                    if (std.mem.eql(u8, name, generic_ident.text()))
                        return .{ .generic = generic.ptr() };
                }
            },
            .params => |params| {
                var params_iter = try params.iter();
                while (params_iter.next()) |param| {
                    const param_ident = try param.ident() orelse continue;
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
        ctx: *Context,

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

pub fn typePtr(ctx: *Context, i: Type.Index) *Type {
    return &ctx.types.items[@intFromEnum(i)];
}

pub fn scopePtr(ctx: *Context, i: Scope.Index) *Scope {
    return &ctx.scopes.items[@intFromEnum(i)];
}

pub fn structPtr(ctx: *Context, i: Struct.Index) *Struct {
    return &ctx.structures.items[@intFromEnum(i)];
}

pub fn fnPtr(ctx: *Context, i: Fn.Index) *Fn {
    return &ctx.functions.items[@intFromEnum(i)];
}

fn err(
    ctx: *Context,
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
    ctx: *Context,
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
    ctx: *Context,
    span: syntax.pure.Span,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!Type.Index {
    try err(ctx, span, fmt, args);
    return Type.get(ctx, .invalid);
}

fn typeTodo(
    ctx: *Context,
    span: syntax.pure.Span,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!Type.Index {
    try todo(ctx, span, src);
    return Type.get(ctx, .invalid);
}

const FormatFnArgs = struct { ctx: *Context, function: Fn.Index };

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

pub fn fmtFn(ctx: *Context, function: Fn.Index) std.fmt.Formatter(formatFn) {
    return .{ .data = .{ .ctx = ctx, .function = function } };
}

const FormatStructArgs = struct { ctx: *Context, structure: Struct.Index };

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

pub fn fmtStruct(ctx: *Context, structure: Struct.Index) std.fmt.Formatter(formatStruct) {
    return .{ .data = .{ .ctx = ctx, .structure = structure } };
}

const FormatTypeArgs = struct { ctx: *Context, ty: Type.Index };

fn formatType(
    args: FormatTypeArgs,
    comptime fmt: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
    return switch (typePtr(args.ctx, args.ty).*) {
        .invalid => writer.print("invalid", .{}),
        .bool => writer.print("bool", .{}),
        .unsigned_integer => |unsigned_integer| writer.print("u{}", .{unsigned_integer.bits}),
        .pointer => |pointee| writer.print("*{}", .{fmtType(args.ctx, pointee)}),
        .structure => |structure| fmtStruct(args.ctx, structure).format(fmt, .{}, writer),
        .function => |function| fmtFn(args.ctx, function).format(fmt, .{}, writer),
    };
}

pub fn fmtType(ctx: *Context, ty: Type.Index) std.fmt.Formatter(formatType) {
    return .{ .data = .{ .ctx = ctx, .ty = ty } };
}

pub fn printDiagnostics(
    ctx: *Context,
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

pub fn deinit(ctx: *Context) void {
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

pub fn dump(ctx: *Context, writer: anytype) (@TypeOf(writer).Error || error{OutOfMemory})!void {
    for (0..ctx.type_pool.entries.len) |i|
        try writer.print("Type {}: {#}\n", .{ i, fmtType(ctx, @enumFromInt(i)) });
    for (0..ctx.functions.items.len) |i|
        try writer.print("{code}\n", .{fmtFn(ctx, @enumFromInt(i))});
}

pub fn findDecl(ctx: Context, pos: syntax.pure.Pos) error{OutOfMemory}!?syntax.ast.Decl {
    var it = try ctx.ast.decls();
    while (it.next()) |decl_syntax| {
        const span = decl_syntax.span();
        if (span.start.offset > pos.offset)
            return null;
        if (span.end.offset <= pos.offset)
            continue;
        return decl_syntax;
    }
    return null;
}

pub fn compile(
    ctx: *Context,
) error{OutOfMemory}!void {
    var it = try ctx.ast.iter();
    while (it.next()) |decl_syntax|
        try analyzeDecl(ctx, decl_syntax);
}

fn analyzeDecl(ctx: *Context, decl: syntax.ast.Decl) error{OutOfMemory}!void {
    switch (decl) {
        .structure => |struct_syntax| {
            var type_index = try Type.get(ctx, .{ .structure = struct_syntax.ptr() });
            var struct_index = typePtr(ctx, type_index).structure;
            var structure = structPtr(ctx, struct_index);
            if (structure.analysis == .unanalyzed) {
                std.debug.assert(structure.fields.entries.len == 0);
                var it = try struct_syntax.iter();
                while (it.next()) |field| {
                    const name_syntax = try field.ident() orelse
                        return err(ctx, field.span(), "struct field without name", .{});

                    const type_syntax = try field.typeExpr() orelse
                        return err(ctx, field.span(), "struct field without type", .{});

                    const ty = try analyzeTypeExpr(ctx, type_syntax);
                    try structure.fields.put(ctx.gpa, name_syntax.text(), ty);
                }
                structure.analysis = .analyzed;
            }
        },
        .function => |function_syntax| {
            var type_index = try Type.get(ctx, .{ .function = function_syntax.ptr() });
            var function_index = typePtr(ctx, type_index).function;
            var function = fnPtr(ctx, function_index);
            if (function.analysis == .unanalyzed) {
                params: {
                    const params = try function_syntax.params() orelse
                        break :params;

                    var it = try params.iter();
                    while (it.next()) |param| {
                        const name_syntax = try param.ident() orelse
                            return err(ctx, param.span(), "function parameter without name", .{});

                        const type_syntax = try param.typeExpr() orelse
                            return err(ctx, param.span(), "function parameter without type", .{});

                        const ty = try analyzeTypeExpr(ctx, type_syntax);
                        try function.params.put(ctx.gpa, name_syntax.text(), ty);
                    }
                }
                returns: {
                    const returns = try function_syntax.returns() orelse
                        break :returns;

                    var it = try returns.iter();
                    while (it.next()) |param| {
                        const name_syntax = try param.ident() orelse
                            return err(ctx, param.span(), "function return without name", .{});

                        const type_syntax = try param.typeExpr() orelse
                            return err(ctx, param.span(), "function return without type", .{});

                        const ty = try analyzeTypeExpr(ctx, type_syntax);
                        try function.returns.put(ctx.gpa, name_syntax.text(), ty);
                    }
                }

                const body = try function_syntax.body() orelse
                    return todo(ctx, function_syntax.span(), @src());

                try checkBlock(ctx, function_index, body);

                function.analysis = .analyzed;
            }
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExpr() orelse
                return err(ctx, constant_syntax.span(), "constant without type", .{});

            const ty = try analyzeTypeExpr(ctx, type_expr);
            const expr = try constant_syntax.expr() orelse
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

// may return a type other than/incompatible with expected_type
fn analyzeExpr(
    ctx: *Context,
    expr: syntax.ast.Expr,
    maybe_expected_type: ?Type.Index,
) error{OutOfMemory}!Type.Index {
    switch (expr) {
        .paren => |paren_expr| {
            const sub_expr = try paren_expr.expr() orelse
                return typeTodo(ctx, paren_expr.span(), @src());
            return analyzeExpr(ctx, sub_expr, maybe_expected_type);
        },
        .literal => |literal_expr| {
            if (try literal_expr.number()) |_| {
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
            const ident = try ident_expr.ident() orelse
                return typeTodo(ctx, ident_expr.span(), @src());

            const scope2 = try Scope.find(ctx, ident_expr.tree);
            const lookup_result = try Scope.lookUp(ctx, scope2, ident.text()) orelse
                return typeErr(ctx, ident_expr.span(), "undefined identifier: {s}", .{ident.text()});

            switch (lookup_result) {
                .decl => |decl| {
                    return typeOfDecl(ctx, try decl.deref(ctx.ast.tree));
                },
                .fn_param => |fn_param_ptr| {
                    const fn_param = try fn_param_ptr.deref(ctx.ast.tree);

                    const type_expr = try fn_param.typeExpr() orelse
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
            const lhs_expr = try binary_expr.lhs() orelse
                return typeErr(ctx, binary_expr.span(), "binary expression missing left-hand side", .{});

            const rhs_expr = try binary_expr.rhs() orelse
                return typeErr(ctx, binary_expr.span(), "binary expression missing right-hand side", .{});

            const lhs_type = try analyzeExpr(ctx, lhs_expr, null);
            const rhs_type = try analyzeExpr(ctx, rhs_expr, null);

            if (try binary_expr.plus() != null or
                try binary_expr.minus() != null or
                try binary_expr.star() != null or
                try binary_expr.slash() != null or
                try binary_expr.percent() != null or
                try binary_expr.lt2() != null or
                try binary_expr.gt2() != null or
                try binary_expr.ampersand() != null or
                try binary_expr.pipe() != null or
                try binary_expr.caret() != null)
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

            if (try binary_expr.eq2() != null or
                try binary_expr.bangEq() != null or
                try binary_expr.lt() != null or
                try binary_expr.ltEq() != null or
                try binary_expr.gt() != null or
                try binary_expr.gtEq() != null)
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
            const fn_expr = try call_expr.expr() orelse
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
            const params = function.params;
            const args_wrapper = try call_expr.args() orelse
                return typeTodo(ctx, call_expr.span(), @src());

            var args = try args_wrapper.iter();
            for (params.values()) |param_ty| {
                const arg = args.next() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_expr = try arg.expr() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_type = try analyzeExpr(ctx, arg_expr, null);
                if (arg_type != param_ty) {
                    return typeTodo(ctx, call_expr.span(), @src());
                }
            }
            if (args.next()) |_|
                return typeTodo(ctx, call_expr.span(), @src());
            if (function.returns.values().len != 1)
                return typeTodo(ctx, call_expr.span(), @src());
            const ret_type = function.returns.values()[0];
            return ret_type;
        },
    }
}

fn analyzeTypeExpr(
    ctx: *Context,
    type_expr: syntax.ast.TypeExpr,
) error{OutOfMemory}!Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = try ident.ident() orelse
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

            const decl = switch (lookup_result) {
                .decl => |decl| try decl.deref(ctx.ast.tree),
                else => return typeTodo(ctx, ident.span(), @src()),
            };

            switch (decl) {
                .structure => |structure| {
                    return Type.get(ctx, .{ .structure = structure.ptr() });
                },
                .function => return typeTodo(ctx, ident.span(), @src()),
                .constant => return typeTodo(ctx, ident.span(), @src()),
            }
        },
        .unary => |unary| {
            const operand_type_expr = try unary.typeExpr() orelse
                return typeErr(ctx, unary.span(), "operator missing operand", .{});

            const operand_type_index = try analyzeTypeExpr(ctx, operand_type_expr);

            if (try unary.star() != null)
                return Type.get(ctx, .{ .pointer = operand_type_index });

            try err(ctx, unary.span(), "unknown binary operator", .{});

            return Type.get(ctx, .invalid);
        },
    }
}

fn typeOfDecl(
    ctx: *Context,
    decl: syntax.ast.Decl,
) error{OutOfMemory}!Type.Index {
    switch (decl) {
        .structure => |struct_syntax| {
            return Type.get(ctx, .{ .structure = struct_syntax.ptr() });
        },
        .function => |function_syntax| {
            return Type.get(ctx, .{ .function = function_syntax.ptr() });
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExpr() orelse
                return typeErr(ctx, constant_syntax.span(), "constant missing type", .{});

            return try analyzeTypeExpr(ctx, type_expr);
        },
    }
}

fn checkBlock(
    ctx: *Context,
    function_index: Fn.Index,
    body: syntax.ast.Stmt.Block,
) error{OutOfMemory}!void {
    const function = fnPtr(ctx, function_index);

    for (try body.tree.children()) |child| {
        if (child != .tree) continue;

        const stmt = syntax.ast.Stmt.cast(child.tree) orelse
            return todo(ctx, function.syntax.span(), @src());

        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = try expr_stmt.expr() orelse
                    return todo(ctx, function.syntax.span(), @src());

                try checkExpr(ctx, function_index, expr, null);
            },
            .block => |block_stmt| {
                try checkBlock(ctx, function_index, block_stmt);
            },
            .@"return" => |return_stmt| {
                var exprs = try return_stmt.iter();
                for (function.returns.values()) |ret_ty| {
                    const expr = exprs.next() orelse
                        return todo(ctx, function.syntax.span(), @src());
                    try checkExpr(ctx, function_index, expr, ret_ty);
                }
                if (exprs.next()) |expr| {
                    try err(ctx, expr.span(), "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                if (try if_stmt.cond()) |if_cond|
                    try checkExpr(ctx, function_index, if_cond, try Type.get(ctx, .bool))
                else
                    return err(ctx, if_stmt.span(), "if statement missing condition", .{});

                if (try if_stmt.thenBody()) |if_body|
                    try checkBlock(ctx, function_index, if_body)
                else
                    return err(ctx, if_stmt.span(), "if statement missing body", .{});
            },
            .loop => |loop_stmt| {
                const loop_body = try loop_stmt.body() orelse
                    return err(ctx, loop_stmt.span(), "loop missing body", .{});

                try checkBlock(ctx, function_index, loop_body);
            },
            .@"while" => |while_stmt| {
                if (try while_stmt.cond()) |while_cond|
                    try checkExpr(ctx, function_index, while_cond, try Type.get(ctx, .bool))
                else
                    return err(ctx, while_stmt.span(), "while statement missing condition", .{});

                if (try while_stmt.body()) |while_body|
                    try checkBlock(ctx, function_index, while_body)
                else
                    return err(ctx, while_stmt.span(), "while statement missing body", .{});
            },
        }
    }
}

fn checkExpr(
    ctx: *Context,
    function: Fn.Index,
    expr: syntax.ast.Expr,
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
