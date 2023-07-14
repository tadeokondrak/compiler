const Context = @This();

const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");
const LineIndex = @import("LineIndex.zig");

gpa: std.mem.Allocator,
ast: syntax.ast.File,
pool: std.AutoArrayHashMapUnmanaged(void, void) = .{},
types: std.ArrayListUnmanaged(Type) = .{},
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

    fn toKey(ctx: *Context, ty: Type) Key {
        return switch (ty) {
            .invalid => .invalid,
            .bool => .bool,
            .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
            .pointer => |pointee| .{ .pointer = pointee },
            .structure => |structure| .{ .structure = structPtr(ctx, structure).syntax },
            .function => |function| .{ .function = fnPtr(ctx, function).syntax },
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
    syntax: syntax.ast.Ptr(syntax.ast.Decl.Struct),
    name: []const u8,
    fields: std.StringArrayHashMapUnmanaged(Type.Index) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

const Fn = struct {
    analysis: enum { unanalyzed, analyzed } = .unanalyzed,
    syntax: syntax.ast.Ptr(syntax.ast.Decl.Fn),
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(struct {
        syntax: syntax.ast.Ptr(syntax.ast.Decl.Fn.Param),
        ty: Type.Index,
    }) = .{},
    returns: std.StringArrayHashMapUnmanaged(struct {
        syntax: syntax.ast.Ptr(syntax.ast.Decl.Fn.Return),
        ty: Type.Index,
    }) = .{},

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

pub const Diagnostic = struct {
    span: syntax.pure.Span,
    message: []const u8,
};

const Scope = struct {
    parent: ?*const Scope,
    getFn: *const fn (self: *const Scope, name: []const u8) ?LookupResult,

    const LookupResult = union(enum) {
        decl: syntax.ast.Ptr(syntax.ast.Decl),
        fn_param: syntax.ast.Ptr(syntax.ast.Decl.Fn.Param),
        true,
        false,
        null,
    };

    pub fn get(scope: *const Scope, name: []const u8) ?LookupResult {
        if (scope.getFn(scope, name)) |i| return i;
        if (scope.parent) |p| return p.get(name);
        return null;
    }

    const Builtin = struct {
        base: Scope = .{
            .parent = null,
            .getFn = Builtin.get,
        },

        fn get(_: *const Scope, name: []const u8) ?LookupResult {
            const map = std.ComptimeStringMap(LookupResult, .{
                .{ "null", .null },
                .{ "true", .true },
                .{ "false", .false },
            });
            return map.get(name);
        }
    };

    const File = struct {
        base: Scope = .{
            .parent = null,
            .getFn = File.get,
        },
        names: *const std.StringArrayHashMapUnmanaged(syntax.ast.Ptr(syntax.ast.Decl)),

        fn get(scope: *const Scope, name: []const u8) ?LookupResult {
            const file = @fieldParentPtr(File, "base", scope);
            const decl = file.names.get(name) orelse
                return null;
            return .{ .decl = decl };
        }
    };

    const Fn = struct {
        base: Scope = .{
            .parent = null,
            .getFn = Scope.Fn.get,
        },
        args: *const std.StringArrayHashMapUnmanaged(syntax.ast.Ptr(syntax.ast.Decl.Fn.Param)),

        fn get(scope: *const Scope, name: []const u8) ?LookupResult {
            const function = @fieldParentPtr(Scope.Fn, "base", scope);
            const param = function.args.get(name) orelse
                return null;

            return .{ .fn_param = param };
        }
    };
};

pub fn typePtr(ctx: *Context, i: Type.Index) *Type {
    return &ctx.types.items[@intFromEnum(i)];
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
    return lookUpType(ctx, .invalid);
}

fn typeTodo(
    ctx: *Context,
    span: syntax.pure.Span,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!Type.Index {
    try todo(ctx, span, src);
    return lookUpType(ctx, .invalid);
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
        try writer.print("{s}: {}", .{ key, fmtType(args.ctx, value.ty) });
    }
    try writer.print(") (", .{});
    for (function.returns.keys(), function.returns.values(), 0..) |key, value, i| {
        if (i > 0) try writer.print(", ", .{});
        try writer.print("{s}: {}", .{ key, fmtType(args.ctx, value.ty) });
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
    ctx.pool.deinit(ctx.gpa);
    ctx.types.deinit(ctx.gpa);
}

pub fn dump(ctx: *Context, writer: anytype) (@TypeOf(writer).Error || error{OutOfMemory})!void {
    for (0..ctx.pool.entries.len) |i|
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
    var names: std.StringArrayHashMapUnmanaged(syntax.ast.Ptr(syntax.ast.Decl)) = .{};
    defer names.deinit(ctx.gpa);

    var it = try ctx.ast.iter();
    while (it.next()) |decl_syntax| {
        const ident = try decl_syntax.ident() orelse
            return err(ctx, decl_syntax.span(), "declaration missing name", .{});

        const name = ident.text();
        try names.put(ctx.gpa, name, .{ .span = decl_syntax.tree().span() });
    }

    var builtin_scope = Scope.Builtin{};
    var file_scope = Scope.File{
        .base = .{ .getFn = Scope.File.get, .parent = &builtin_scope.base },
        .names = &names,
    };

    for (names.values()) |value|
        try analyzeDecl(ctx, &file_scope.base, try value.deref(ctx.ast.tree));
}

fn analyzeDecl(ctx: *Context, scope: *const Scope, decl: syntax.ast.Decl) error{OutOfMemory}!void {
    switch (decl) {
        .structure => |struct_syntax| {
            var type_index = try lookUpType(ctx, .{ .structure = struct_syntax.ptr() });
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

                    const ty = try analyzeTypeExpr(ctx, scope, type_syntax);
                    try structure.fields.put(ctx.gpa, name_syntax.text(), ty);
                }
                structure.analysis = .analyzed;
            }
        },
        .function => |function_syntax| {
            var type_index = try lookUpType(ctx, .{ .function = function_syntax.ptr() });
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

                        const ty = try analyzeTypeExpr(ctx, scope, type_syntax);
                        try function.params.put(ctx.gpa, name_syntax.text(), .{
                            .syntax = param.ptr(),
                            .ty = ty,
                        });
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

                        const ty = try analyzeTypeExpr(ctx, scope, type_syntax);
                        try function.returns.put(ctx.gpa, name_syntax.text(), .{
                            .syntax = param.ptr(),
                            .ty = ty,
                        });
                    }
                }
                try checkFnBody(ctx, scope, function_index, function_syntax);
                function.analysis = .analyzed;
            }
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExpr() orelse
                return err(ctx, constant_syntax.span(), "constant without type", .{});

            const ty = try analyzeTypeExpr(ctx, scope, type_expr);
            const expr = try constant_syntax.expr() orelse
                return err(ctx, constant_syntax.span(), "constant without initializer", .{});

            const expr_ty = try analyzeExpr(ctx, scope, expr, ty);
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
    scope: *const Scope,
    expr: syntax.ast.Expr,
    maybe_expected_type: ?Type.Index,
) error{OutOfMemory}!Type.Index {
    switch (expr) {
        .paren => |paren_expr| {
            const sub_expr = try paren_expr.expr() orelse
                return typeTodo(ctx, paren_expr.span(), @src());
            return analyzeExpr(ctx, scope, sub_expr, maybe_expected_type);
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
                    return lookUpType(ctx, .{ .unsigned_integer = .{ .bits = 32 } });
                }
            }

            return typeTodo(ctx, literal_expr.span(), @src());
        },
        .ident => |ident_expr| {
            const ident = try ident_expr.ident() orelse
                return typeTodo(ctx, ident_expr.span(), @src());

            const name = ident.text();
            const lookup_result = scope.get(name) orelse
                return typeErr(ctx, ident_expr.span(), "undefined identifier: {s}", .{name});

            switch (lookup_result) {
                .decl => |decl| {
                    const root_scope = scope; // TODO
                    return typeOfDecl(ctx, root_scope, try decl.deref(ctx.ast.tree));
                },
                .fn_param => |fn_param_ptr| {
                    const fn_param = try fn_param_ptr.deref(ctx.ast.tree);

                    const type_expr = try fn_param.typeExpr() orelse
                        return typeTodo(ctx, ident_expr.span(), @src());

                    return try analyzeTypeExpr(ctx, scope, type_expr);
                },
                .true, .false => return lookUpType(ctx, .bool),
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

            const lhs_type = try analyzeExpr(ctx, scope, lhs_expr, null);
            const rhs_type = try analyzeExpr(ctx, scope, rhs_expr, null);

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
                return lookUpType(ctx, .invalid);
            }

            if (try binary_expr.eq2() != null or
                try binary_expr.bangEq() != null or
                try binary_expr.lt() != null or
                try binary_expr.ltEq() != null or
                try binary_expr.gt() != null or
                try binary_expr.gtEq() != null)
            {
                if (lhs_type == rhs_type)
                    return lookUpType(ctx, .bool);
                try err(
                    ctx,
                    binary_expr.span(),
                    "comparison operator type mismatch: lhs {}, rhs {}",
                    .{ fmtType(ctx, lhs_type), fmtType(ctx, rhs_type) },
                );
                return lookUpType(ctx, .invalid);
            }

            return typeTodo(ctx, binary_expr.span(), @src());
        },
        .call => |call_expr| {
            const fn_expr = try call_expr.expr() orelse
                return typeTodo(ctx, call_expr.span(), @src());

            const fn_type_index = try analyzeExpr(ctx, scope, fn_expr, null);
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
            for (params.values()) |param| {
                const arg = args.next() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_expr = try arg.expr() orelse
                    return typeTodo(ctx, call_expr.span(), @src());

                const arg_type = try analyzeExpr(ctx, scope, arg_expr, null);
                if (arg_type != param.ty) {
                    return typeTodo(ctx, call_expr.span(), @src());
                }
            }
            if (args.next()) |_|
                return typeTodo(ctx, call_expr.span(), @src());
            if (function.returns.values().len != 1)
                return typeTodo(ctx, call_expr.span(), @src());
            const ret_type = function.returns.values()[0].ty;
            return ret_type;
        },
    }
}

fn analyzeTypeExpr(
    ctx: *Context,
    scope: *const Scope,
    type_expr: syntax.ast.TypeExpr,
) error{OutOfMemory}!Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = try ident.ident() orelse
                return typeTodo(ctx, ident.span(), @src());

            const ident_text = ident_token.text();
            if (ident_text.len > 0 and ident_text[0] == 'u') {
                if (std.fmt.parseInt(u32, ident_text[1..], 10)) |bits| {
                    return lookUpType(ctx, .{ .unsigned_integer = .{ .bits = bits } });
                } else |e| switch (e) {
                    error.Overflow => return typeTodo(ctx, ident.span(), @src()),
                    error.InvalidCharacter => {},
                }
            }

            const lookup_result = scope.get(ident_text) orelse
                return typeErr(ctx, ident.span(), "undefined identifier {s}", .{ident_text});

            const decl = switch (lookup_result) {
                .decl => |decl| try decl.deref(ctx.ast.tree),
                else => return typeTodo(ctx, ident.span(), @src()),
            };

            switch (decl) {
                .structure => |structure| {
                    return lookUpType(ctx, .{ .structure = structure.ptr() });
                },
                .function => return typeTodo(ctx, ident.span(), @src()),
                .constant => return typeTodo(ctx, ident.span(), @src()),
            }
        },
        .unary => |unary| {
            const operand_type_expr = try unary.typeExpr() orelse
                return typeErr(ctx, unary.span(), "operator missing operand", .{});

            const operand_type_index = try analyzeTypeExpr(ctx, scope, operand_type_expr);

            if (try unary.star() != null)
                return lookUpType(ctx, .{ .pointer = operand_type_index });

            try err(ctx, unary.span(), "unknown binary operator", .{});

            return lookUpType(ctx, .invalid);
        },
    }
}

fn typeOfDecl(
    ctx: *Context,
    root_scope: *const Scope,
    decl: syntax.ast.Decl,
) error{OutOfMemory}!Type.Index {
    switch (decl) {
        .structure => |struct_syntax| {
            return lookUpType(ctx, .{ .structure = struct_syntax.ptr() });
        },
        .function => |function_syntax| {
            return lookUpType(ctx, .{ .function = function_syntax.ptr() });
        },
        .constant => |constant_syntax| {
            const type_expr = try constant_syntax.typeExpr() orelse
                return typeErr(ctx, constant_syntax.span(), "constant missing type", .{});

            return try analyzeTypeExpr(ctx, root_scope, type_expr);
        },
    }
}

pub fn lookUpType(ctx: *Context, key: Type.Key) error{OutOfMemory}!Type.Index {
    const result = try ctx.pool.getOrPutAdapted(
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

                try ctx.structures.append(ctx.gpa, .{ .syntax = structure.ptr(), .name = ident.text() });
                break :blk .{ .structure = @enumFromInt(struct_index) };
            },
            .function => |function_ptr| blk: {
                const function = try function_ptr.deref(ctx.ast.tree);

                const function_index = ctx.functions.items.len;
                const ident = try function.ident() orelse
                    return typeTodo(ctx, function.span(), @src());

                try ctx.functions.append(ctx.gpa, .{ .syntax = function.ptr(), .name = ident.text() });
                break :blk .{ .function = @enumFromInt(function_index) };
            },
        });
    }
    return @enumFromInt(result.index);
}

fn checkFnBody(
    ctx: *Context,
    scope: *const Scope,
    function_index: Fn.Index,
    function_syntax: syntax.ast.Decl.Fn,
) error{OutOfMemory}!void {
    const function = fnPtr(ctx, function_index);
    _ = function;

    const body = try function_syntax.body() orelse
        return todo(ctx, function_syntax.span(), @src());

    var args: std.StringArrayHashMapUnmanaged(syntax.ast.Ptr(syntax.ast.Decl.Fn.Param)) = .{};
    defer args.deinit(ctx.gpa);

    const params = try function_syntax.params() orelse
        return todo(ctx, function_syntax.span(), @src());
    var it = try params.iter();
    while (it.next()) |param| {
        const name_syntax = try param.ident() orelse
            return todo(ctx, function_syntax.span(), @src());
        const name = name_syntax.text();
        try args.put(ctx.gpa, name, param.ptr());
    }

    const fn_scope: Scope.Fn = .{
        .base = .{ .parent = scope, .getFn = Scope.Fn.get },
        .args = &args,
    };
    try checkBlock(ctx, &fn_scope.base, function_index, body);
}

fn checkBlock(
    ctx: *Context,
    scope: *const Scope,
    function_index: Fn.Index,
    body: syntax.ast.Stmt.Block,
) error{OutOfMemory}!void {
    const function = fnPtr(ctx, function_index);

    for (try body.tree.children()) |child| {
        if (child != .tree) continue;

        const stmt = syntax.ast.Stmt.cast(child.tree) orelse
            return todo(ctx, function.syntax.span, @src());

        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = try expr_stmt.expr() orelse
                    return todo(ctx, function.syntax.span, @src());

                try checkExpr(ctx, scope, function_index, expr, null);
            },
            .block => |block_stmt| {
                try checkBlock(ctx, scope, function_index, block_stmt);
            },
            .@"return" => |return_stmt| {
                var exprs = try return_stmt.iter();
                for (function.returns.values()) |ret| {
                    const expr = exprs.next() orelse
                        return todo(ctx, function.syntax.span, @src());
                    try checkExpr(ctx, scope, function_index, expr, ret.ty);
                }
                if (exprs.next()) |expr| {
                    try err(ctx, expr.span(), "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                if (try if_stmt.cond()) |if_cond|
                    try checkExpr(ctx, scope, function_index, if_cond, try lookUpType(ctx, .bool))
                else
                    return err(ctx, if_stmt.span(), "if statement missing condition", .{});

                if (try if_stmt.thenBody()) |if_body|
                    try checkBlock(ctx, scope, function_index, if_body)
                else
                    return err(ctx, if_stmt.span(), "if statement missing body", .{});
            },
            .loop => |loop_stmt| {
                const loop_body = try loop_stmt.body() orelse
                    return err(ctx, loop_stmt.span(), "loop missing body", .{});

                try checkBlock(ctx, scope, function_index, loop_body);
            },
            .@"while" => |while_stmt| {
                if (try while_stmt.cond()) |while_cond|
                    try checkExpr(ctx, scope, function_index, while_cond, try lookUpType(ctx, .bool))
                else
                    return err(ctx, while_stmt.span(), "while statement missing condition", .{});

                if (try while_stmt.body()) |while_body|
                    try checkBlock(ctx, scope, function_index, while_body)
                else
                    return err(ctx, while_stmt.span(), "while statement missing body", .{});
            },
        }
    }
}

fn checkExpr(
    ctx: *Context,
    scope: *const Scope,
    function: Fn.Index,
    expr: syntax.ast.Expr,
    maybe_expected_type: ?Type.Index,
) error{OutOfMemory}!void {
    _ = function;
    const ty = try analyzeExpr(ctx, scope, expr, maybe_expected_type);
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
