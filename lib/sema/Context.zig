const Context = @This();

const std = @import("std");
const syntax = @import("syntax");
const parse = @import("parse");
const ir = @import("ir.zig");
const LineIndex = @import("LineIndex.zig");

gpa: std.mem.Allocator,
root: syntax.pure.Root,
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
        structure: syntax.ast.Decl.Struct,
        function: syntax.ast.Decl.Fn,
    };

    fn toKey(ctx: *Context, ty: Type) Key {
        return switch (ty) {
            .invalid => .invalid,
            .bool => .bool,
            .unsigned_integer => |data| .{ .unsigned_integer = .{ .bits = data.bits } },
            .pointer => |pointee| .{ .pointer = pointee },
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
    analysis: enum { unanalyzed, analyzed, generated } = .unanalyzed,
    syntax: syntax.ast.Decl.Fn,
    name: []const u8,
    params: std.StringArrayHashMapUnmanaged(struct {
        syntax: syntax.ast.Decl.Fn.Param,
        ty: Type.Index,
    }) = .{},
    returns: std.StringArrayHashMapUnmanaged(struct {
        syntax: syntax.ast.Decl.Fn.Return,
        ty: Type.Index,
    }) = .{},
    func: ir.Func = undefined,

    const Index = enum(usize) {
        invalid = std.math.maxInt(usize),
        _,
    };
};

const Diagnostic = struct {
    span: syntax.pure.Span,
    message: []const u8,
};

const Scope = struct {
    parent: ?*const Scope,
    getFn: *const fn (self: *const Scope, name: []const u8) ?LookupResult,

    const LookupResult = union(enum) {
        decl: syntax.ast.Decl,
        fn_param: syntax.ast.Decl.Fn.Param,
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
        names: *const std.StringArrayHashMapUnmanaged(syntax.ast.Decl),

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
        args: *const std.StringArrayHashMapUnmanaged(syntax.ast.Decl.Fn.Param),

        fn get(scope: *const Scope, name: []const u8) ?LookupResult {
            const function = @fieldParentPtr(Scope.Fn, "base", scope);
            const param = function.args.get(name) orelse
                return null;

            return .{ .fn_param = param };
        }
    };
};

const Gen = struct {
    vars: std.AutoHashMapUnmanaged(syntax.pure.Tree.Index, ir.Reg) = .{},
};

const GenValue = union(enum) {
    invalid,
    void,
    reg: ir.Reg,
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
    tree: syntax.pure.Tree.Index,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!void {
    return ctx.diagnostics.append(ctx.gpa, .{
        .span = ctx.root.treeSpan(tree),
        .message = try std.fmt.allocPrint(ctx.gpa, fmt, args),
    });
}

fn todo(
    ctx: *Context,
    tree: syntax.pure.Tree.Index,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!void {
    return ctx.err(
        tree,
        "TODO in {s} at {s}:{}:{}",
        .{ src.fn_name, src.file, src.line, src.column },
    );
}

fn typeErr(
    ctx: *Context,
    tree: syntax.pure.Tree.Index,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!Type.Index {
    try ctx.err(tree, fmt, args);
    return ctx.lookUpType(.invalid);
}

fn typeTodo(
    ctx: *Context,
    tree: syntax.pure.Tree.Index,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!Type.Index {
    try ctx.todo(tree, src);
    return ctx.lookUpType(.invalid);
}

fn genErr(
    ctx: *Context,
    tree: syntax.pure.Tree.Index,
    comptime fmt: []const u8,
    args: anytype,
) error{OutOfMemory}!GenValue {
    try ctx.err(tree, fmt, args);
    return .invalid;
}

fn genTodo(
    ctx: *Context,
    tree: syntax.pure.Tree.Index,
    src: std.builtin.SourceLocation,
) error{OutOfMemory}!GenValue {
    try ctx.todo(tree, src);
    return .invalid;
}

const FormatFnArgs = struct { ctx: *Context, function: Fn.Index };

fn formatFn(
    args: FormatFnArgs,
    comptime fmt: []const u8,
    _: std.fmt.FormatOptions,
    writer: anytype,
) @TypeOf(writer).Error!void {
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
    return switch (args.ctx.typePtr(args.ty).*) {
        .invalid => writer.print("invalid", .{}),
        .bool => writer.print("bool", .{}),
        .unsigned_integer => |unsigned_integer| writer.print("u{}", .{unsigned_integer.bits}),
        .pointer => |pointee| writer.print("*{}", .{args.ctx.fmtType(pointee)}),
        .structure => |structure| args.ctx.fmtStruct(structure).format(fmt, .{}, writer),
        .function => |function| args.ctx.fmtFn(function).format(fmt, .{}, writer),
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
        const line_end = line_index.newlines[start.line];
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

pub fn init(allocator: std.mem.Allocator, src: []const u8) !Context {
    var parsed = try parse.parseFile(allocator, src);
    errdefer parsed.root.deinit(allocator);
    var context: Context = .{
        .gpa = allocator,
        .root = parsed.root,
        .ast = parsed.ast,
    };
    for (
        parsed.root.errors.items(.message),
        parsed.root.errors.items(.span),
    ) |message, span| {
        // TODO: don't leak memory on failure here
        try context.diagnostics.append(allocator, .{
            .message = try allocator.dupe(u8, message),
            .span = span,
        });
    }
    return context;
}

pub fn deinit(ctx: *Context) void {
    for (ctx.diagnostics.items(.message)) |message|
        ctx.gpa.free(message);
    ctx.diagnostics.deinit(ctx.gpa);
    for (ctx.functions.items) |*function| {
        if (function.analysis == .generated)
            function.func.deinit(ctx.gpa);
        function.params.deinit(ctx.gpa);
        function.returns.deinit(ctx.gpa);
    }
    for (ctx.structures.items) |*structure|
        structure.fields.deinit(ctx.gpa);
    ctx.structures.deinit(ctx.gpa);
    ctx.functions.deinit(ctx.gpa);
    ctx.pool.deinit(ctx.gpa);
    ctx.types.deinit(ctx.gpa);
    ctx.root.deinit(ctx.gpa);
}

pub fn dump(ctx: *Context, writer: anytype) (@TypeOf(writer).Error || error{OutOfMemory})!void {
    for (0..ctx.pool.entries.len) |i|
        try writer.print("Type {}: {#}\n", .{ i, ctx.fmtType(@enumFromInt(i)) });
    for (0..ctx.functions.items.len) |i|
        try writer.print("{code}\n", .{ctx.fmtFn(@enumFromInt(i))});
}

pub fn findDecl(ctx: *Context, pos: syntax.pure.Pos) ?syntax.ast.Decl {
    var it = ctx.ast.decls(ctx.root);
    while (it.next(ctx.root)) |decl_syntax| {
        const span = ctx.root.treeSpan(decl_syntax.tree());
        if (span.start.offset > pos.offset)
            return null;
        if (span.end.offset <= pos.offset)
            continue;
        return decl_syntax;
    }
    return null;
}

pub fn compile(ctx: *Context) error{OutOfMemory}!void {
    var names: std.StringArrayHashMapUnmanaged(syntax.ast.Decl) = .{};
    defer names.deinit(ctx.gpa);

    {
        var it = ctx.ast.decls(ctx.root);
        while (it.next(ctx.root)) |decl_syntax| {
            const ident = decl_syntax.ident(ctx.root) orelse
                return ctx.err(decl_syntax.tree(), "declaration missing name", .{});

            const name = ctx.root.tokenText(ident);
            try names.put(ctx.gpa, name, decl_syntax);
        }
    }

    var builtin_scope = Scope.Builtin{};
    var file_scope = Scope.File{
        .base = .{ .getFn = Scope.File.get, .parent = &builtin_scope.base },
        .names = &names,
    };

    for (names.values()) |value|
        try analyzeDecl(ctx, &file_scope.base, value);

    for (names.values()) |decl| {
        switch (decl) {
            .function => |function_syntax| {
                var type_index = try ctx.lookUpType(.{ .function = function_syntax });
                var function_index = typePtr(ctx, type_index).function;
                var function = fnPtr(ctx, function_index);

                std.debug.assert(function.analysis == .analyzed);

                const body = function_syntax.body(ctx.root) orelse
                    return ctx.err(function.syntax.tree, "function missing body", .{});

                var args: std.StringArrayHashMapUnmanaged(syntax.ast.Decl.Fn.Param) = .{};
                defer args.deinit(ctx.gpa);

                var fn_scope = Scope.Fn{
                    .base = .{ .parent = &file_scope.base, .getFn = Scope.Fn.get },
                    .args = &args,
                };

                var builder: ir.Builder = .{ .allocator = ctx.gpa };

                var gen = Gen{};
                defer gen.vars.deinit(ctx.gpa);

                {
                    errdefer builder.func.deinit(ctx.gpa);
                    var params: std.ArrayListUnmanaged(ir.Block.Param) = .{};
                    defer params.deinit(ctx.gpa);
                    for (function.params.keys(), function.params.values()) |name, param| {
                        const reg = builder.addReg();
                        try params.append(ctx.gpa, .{
                            .ty = ctx.irType(param.ty),
                            .reg = reg,
                        });
                        try args.put(ctx.gpa, name, param.syntax);
                        try gen.vars.put(ctx.gpa, param.syntax.tree, reg);
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

fn analyzeDecl(ctx: *Context, scope: *const Scope, decl: syntax.ast.Decl) error{OutOfMemory}!void {
    switch (decl) {
        .structure => |struct_syntax| {
            var type_index = try ctx.lookUpType(.{ .structure = struct_syntax });
            var struct_index = typePtr(ctx, type_index).structure;
            var structure = structPtr(ctx, struct_index);
            if (structure.analysis == .unanalyzed) {
                std.debug.assert(structure.fields.entries.len == 0);
                var it = struct_syntax.fields(ctx.root);
                while (it.next(ctx.root)) |field| {
                    const name_syntax = field.ident(ctx.root) orelse
                        return ctx.err(field.tree, "struct field without name", .{});

                    const name = ctx.root.tokenText(name_syntax);
                    const type_syntax = field.typeExpr(ctx.root) orelse
                        return ctx.err(field.tree, "struct field without type", .{});

                    const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                    try structure.fields.put(ctx.gpa, name, ty);
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
                    const params = function_syntax.params(ctx.root) orelse
                        break :params;

                    var it = params.params(ctx.root);
                    while (it.next(ctx.root)) |param| {
                        const name_syntax = param.ident(ctx.root) orelse
                            return ctx.err(param.tree, "function parameter without name", .{});

                        const name = ctx.root.tokenText(name_syntax);
                        const type_syntax = param.typeExpr(ctx.root) orelse
                            return ctx.err(param.tree, "function parameter without type", .{});

                        const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                        try function.params.put(ctx.gpa, name, .{
                            .syntax = param,
                            .ty = ty,
                        });
                    }
                }
                returns: {
                    const returns = function_syntax.returns(ctx.root) orelse
                        break :returns;

                    var it = returns.returns(ctx.root);
                    while (it.next(ctx.root)) |param| {
                        const name_syntax = param.ident(ctx.root) orelse
                            return ctx.err(param.tree, "function return without name", .{});

                        const name = ctx.root.tokenText(name_syntax);
                        const type_syntax = param.typeExpr(ctx.root) orelse
                            return ctx.err(param.tree, "function return without type", .{});

                        const ty = try ctx.analyzeTypeExpr(scope, type_syntax);
                        try function.returns.put(ctx.gpa, name, .{
                            .syntax = param,
                            .ty = ty,
                        });
                    }
                }
                try ctx.checkFnBody(scope, function_index);
                function.analysis = .analyzed;
            }
        },
        .constant => |constant_syntax| {
            const type_expr = constant_syntax.typeExpr(ctx.root) orelse
                return ctx.err(constant_syntax.tree, "constant without type", .{});

            const ty = try ctx.analyzeTypeExpr(scope, type_expr);
            const expr = constant_syntax.expr(ctx.root) orelse
                return ctx.err(constant_syntax.tree, "constant without initializer", .{});

            const expr_ty = try ctx.analyzeExpr(scope, expr, ty);
            if (ty != expr_ty) {
                try ctx.err(expr.tree(), "expected {}, got {}", .{
                    ctx.fmtType(ty),
                    ctx.fmtType(expr_ty),
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
            const sub_expr = paren_expr.expr(ctx.root) orelse
                return ctx.typeTodo(paren_expr.tree, @src());
            return analyzeExpr(ctx, scope, sub_expr, maybe_expected_type);
        },
        .literal => |literal_expr| {
            if (literal_expr.number(ctx.root)) |_| {
                if (maybe_expected_type) |expected_type| {
                    if (ctx.typePtr(expected_type).* == .unsigned_integer)
                        return expected_type;

                    return ctx.typeTodo(literal_expr.tree, @src());
                } else {
                    return ctx.lookUpType(.{ .unsigned_integer = .{ .bits = 32 } });
                }
            }
            return ctx.typeTodo(literal_expr.tree, @src());
        },
        .ident => |ident_expr| {
            const ident = ident_expr.ident(ctx.root) orelse
                return ctx.typeTodo(ident_expr.tree, @src());

            const name = ctx.root.tokenText(ident);
            const lookup_result = scope.get(name) orelse
                return ctx.typeErr(ident_expr.tree, "undefined identifier: {s}", .{name});

            switch (lookup_result) {
                .decl => |decl| {
                    const root_scope = scope; // TODO
                    return typeOfDecl(ctx, root_scope, decl);
                },
                .fn_param => |fn_param| {
                    const type_expr = fn_param.typeExpr(ctx.root) orelse
                        return ctx.typeTodo(ident_expr.tree, @src());

                    return try ctx.analyzeTypeExpr(scope, type_expr);
                },
                .true, .false => return ctx.lookUpType(.bool),
                .null => {
                    if (maybe_expected_type) |expected_type|
                        if (ctx.typePtr(expected_type).* == .pointer)
                            return expected_type;
                    return ctx.typeTodo(ident_expr.tree, @src());
                },
            }
        },
        .unary => |unary_expr| {
            return ctx.typeTodo(unary_expr.tree, @src());
        },
        .binary => |binary_expr| {
            const lhs_expr = binary_expr.lhs(ctx.root) orelse
                return ctx.typeTodo(binary_expr.tree, @src());

            const rhs_expr = binary_expr.rhs(ctx.root) orelse
                return ctx.typeTodo(binary_expr.tree, @src());

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
                try ctx.err(
                    binary_expr.tree,
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
                try ctx.err(
                    binary_expr.tree,
                    "comparison operator type mismatch: lhs {}, rhs {}",
                    .{ ctx.fmtType(lhs_type), ctx.fmtType(rhs_type) },
                );
                return ctx.lookUpType(.invalid);
            }

            return ctx.typeTodo(binary_expr.tree, @src());
        },
        .call => |call_expr| {
            const fn_expr = call_expr.expr(ctx.root) orelse
                return ctx.typeTodo(call_expr.tree, @src());

            const fn_type_index = try analyzeExpr(ctx, scope, fn_expr, null);
            const fn_type = ctx.typePtr(fn_type_index);
            if (fn_type.* != .function) {
                return ctx.typeErr(
                    call_expr.tree,
                    "can't call non-function {}",
                    .{ctx.fmtType(fn_type_index)},
                );
            }

            const function = ctx.fnPtr(fn_type.function);
            const params = function.params;
            const args_wrapper = call_expr.args(ctx.root) orelse
                return ctx.typeTodo(call_expr.tree, @src());

            var args = args_wrapper.args(ctx.root);
            for (params.values()) |param| {
                const arg = args.next(ctx.root) orelse
                    return ctx.typeTodo(call_expr.tree, @src());

                const arg_expr = arg.expr(ctx.root) orelse
                    return ctx.typeTodo(call_expr.tree, @src());

                const arg_type = try analyzeExpr(ctx, scope, arg_expr, null);
                if (arg_type != param.ty) {
                    return ctx.typeTodo(call_expr.tree, @src());
                }
            }
            if (args.next(ctx.root)) |_|
                return ctx.typeTodo(call_expr.tree, @src());
            if (function.returns.values().len != 1)
                return ctx.typeTodo(call_expr.tree, @src());
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
            const ident_token = ident.ident(ctx.root) orelse
                return ctx.typeTodo(ident.tree, @src());

            const ident_text = ctx.root.tokenText(ident_token);
            if (ident_text.len > 0 and ident_text[0] == 'u') {
                if (std.fmt.parseInt(u32, ident_text[1..], 10)) |bits| {
                    return ctx.lookUpType(.{ .unsigned_integer = .{ .bits = bits } });
                } else |e| switch (e) {
                    error.Overflow => return ctx.typeTodo(ident.tree, @src()),
                    error.InvalidCharacter => {},
                }
            }
            const lookup_result = scope.get(ident_text) orelse
                return ctx.typeTodo(ident.tree, @src());

            const decl = switch (lookup_result) {
                .decl => |decl| decl,
                else => return ctx.typeTodo(ident.tree, @src()),
            };

            switch (decl) {
                .structure => |structure| {
                    return ctx.lookUpType(.{ .structure = structure });
                },
                .function => return ctx.typeTodo(ident.tree, @src()),
                .constant => return ctx.typeTodo(ident.tree, @src()),
            }
        },
        .unary => |unary| {
            const operand_type_expr = unary.typeExpr(ctx.root) orelse
                return ctx.typeErr(unary.tree, "operator missing operand", .{});

            const operand_type_index = try analyzeTypeExpr(ctx, scope, operand_type_expr);

            if (unary.star(ctx.root) != null)
                return ctx.lookUpType(.{ .pointer = operand_type_index });

            try ctx.err(unary.tree, "unknown binary operator", .{});

            return ctx.lookUpType(.invalid);
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
            return ctx.lookUpType(.{ .structure = struct_syntax });
        },
        .function => |function_syntax| {
            return ctx.lookUpType(.{ .function = function_syntax });
        },
        .constant => |constant_syntax| {
            const type_expr = constant_syntax.typeExpr(ctx.root) orelse
                return ctx.typeErr(constant_syntax.tree, "constant missing type", .{});

            return try ctx.analyzeTypeExpr(root_scope, type_expr);
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
            .structure => |structure| blk: {
                const struct_index = ctx.structures.items.len;
                const ident = structure.ident(ctx.root) orelse
                    return ctx.typeTodo(structure.tree, @src());

                const name = ctx.root.tokenText(ident);
                try ctx.structures.append(ctx.gpa, .{ .syntax = structure, .name = name });
                break :blk .{ .structure = @enumFromInt(struct_index) };
            },
            .function => |function| blk: {
                const function_index = ctx.functions.items.len;
                const ident = function.ident(ctx.root) orelse
                    return ctx.typeTodo(function.tree, @src());

                const name = ctx.root.tokenText(ident);
                try ctx.functions.append(ctx.gpa, .{ .syntax = function, .name = name });
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
) error{OutOfMemory}!void {
    const function = ctx.fnPtr(function_index);

    const body = function.syntax.body(ctx.root) orelse
        return ctx.todo(function.syntax.tree, @src());

    var args: std.StringArrayHashMapUnmanaged(syntax.ast.Decl.Fn.Param) = .{};
    defer args.deinit(ctx.gpa);

    const params = function.syntax.params(ctx.root) orelse
        return ctx.todo(function.syntax.tree, @src());
    var it = params.params(ctx.root);
    while (it.next(ctx.root)) |param| {
        const name_syntax = param.ident(ctx.root) orelse
            return ctx.todo(function.syntax.tree, @src());
        const name = ctx.root.tokenText(name_syntax);
        try args.put(ctx.gpa, name, param);
    }

    const fn_scope: Scope.Fn = .{
        .base = .{ .parent = scope, .getFn = Scope.Fn.get },
        .args = &args,
    };
    try ctx.checkBlock(&fn_scope.base, function_index, body);
}

fn checkBlock(
    ctx: *Context,
    scope: *const Scope,
    function_index: Fn.Index,
    body: syntax.ast.Stmt.Block,
) error{OutOfMemory}!void {
    const function = ctx.fnPtr(function_index);

    for (ctx.root.treeChildren(body.tree)) |child| {
        const child_tree = child.asTree() orelse continue;

        const stmt = syntax.ast.Stmt.cast(ctx.root, child_tree) orelse
            return ctx.todo(function.syntax.tree, @src());

        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = expr_stmt.expr(ctx.root) orelse
                    return ctx.todo(function.syntax.tree, @src());

                try checkExpr(ctx, scope, function_index, expr, null);
            },
            .block => |block_stmt| {
                try ctx.checkBlock(scope, function_index, block_stmt);
            },
            .@"return" => |return_stmt| {
                var exprs = return_stmt.exprs(ctx.root);
                for (function.returns.values()) |ret| {
                    const expr = exprs.next(ctx.root) orelse
                        return ctx.todo(function.syntax.tree, @src());
                    try checkExpr(ctx, scope, function_index, expr, ret.ty);
                }
                if (exprs.next(ctx.root)) |expr| {
                    try ctx.err(expr.tree(), "too many return values", .{});
                    return;
                }
            },
            .@"if" => |if_stmt| {
                if (if_stmt.cond(ctx.root)) |if_cond|
                    try checkExpr(ctx, scope, function_index, if_cond, try ctx.lookUpType(.bool))
                else
                    return ctx.err(if_stmt.tree, "if statement missing condition", .{});

                if (if_stmt.thenBody(ctx.root)) |if_body|
                    try ctx.checkBlock(scope, function_index, if_body)
                else
                    return ctx.err(if_stmt.tree, "if statement missing body", .{});
            },
            .loop => |loop_stmt| {
                const loop_body = loop_stmt.body(ctx.root) orelse
                    return ctx.err(loop_stmt.tree, "loop missing body", .{});

                try ctx.checkBlock(scope, function_index, loop_body);
            },
            .@"while" => |while_stmt| {
                if (while_stmt.cond(ctx.root)) |while_cond|
                    try checkExpr(ctx, scope, function_index, while_cond, try ctx.lookUpType(.bool))
                else
                    return ctx.err(while_stmt.tree, "while statement missing condition", .{});

                if (while_stmt.body(ctx.root)) |while_body|
                    try ctx.checkBlock(scope, function_index, while_body)
                else
                    return ctx.err(while_stmt.tree, "while statement missing body", .{});
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
    const ty = try ctx.analyzeExpr(scope, expr, maybe_expected_type);
    if (maybe_expected_type) |expected_type| {
        if (ty != expected_type) {
            try ctx.err(
                expr.tree(),
                "expected {}, got {}",
                .{ ctx.fmtType(expected_type), ctx.fmtType(ty) },
            );
        }
    }
}

fn genBlock(
    ctx: *Context,
    gen: *Gen,
    scope: *const Scope,
    block: syntax.ast.Stmt.Block,
    builder: *ir.Builder,
) error{OutOfMemory}!void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        const child_tree = child.asTree() orelse continue;

        const stmt = syntax.ast.Stmt.cast(ctx.root, child_tree) orelse
            return ctx.todo(child_tree, @src());

        switch (stmt) {
            .expr => |expr_stmt| {
                const expr = expr_stmt.expr(ctx.root) orelse
                    return ctx.todo(expr_stmt.tree, @src());

                _ = try genExpr(ctx, gen, scope, expr, builder);
            },
            .block => |nested_block| {
                return ctx.genBlock(gen, scope, nested_block, builder);
            },
            .@"return" => |return_stmt| {
                var exprs = return_stmt.exprs(ctx.root);
                var regs: std.ArrayListUnmanaged(ir.Reg) = .{};
                defer regs.deinit(ctx.gpa);
                while (exprs.next(ctx.root)) |expr| {
                    const value = try genExpr(ctx, gen, scope, expr, builder);
                    if (value != .reg) {
                        try ctx.err(expr.tree(), "cannot use void value", .{});
                        return;
                    }
                    try regs.append(ctx.gpa, value.reg);
                }
                return builder.buildRet(regs.items);
            },
            .@"if" => |if_stmt| {
                const cond = if_stmt.cond(ctx.root) orelse
                    return ctx.todo(if_stmt.tree, @src());

                const cond_value = try genExpr(ctx, gen, scope, cond, builder);
                if (cond_value != .reg) {
                    try ctx.err(cond.tree(), "cannot use value", .{});
                    return;
                }

                const then_block = try builder.addBlock(&.{});
                const cont_block = try builder.addBlock(&.{});

                if (if_stmt.elseToken(ctx.root) != null) {
                    const else_block = try builder.addBlock(&.{});

                    try builder.buildBranch(cond_value.reg, then_block, else_block);

                    builder.switchToBlock(then_block);
                    const then_body = if_stmt.thenBody(ctx.root) orelse
                        return ctx.todo(if_stmt.tree, @src());
                    try ctx.genBlock(gen, scope, then_body, builder);
                    try builder.buildJump(cont_block);

                    builder.switchToBlock(else_block);
                    if (if_stmt.elseBody(ctx.root)) |else_body|
                        try ctx.genBlock(gen, scope, else_body, builder);
                } else {
                    try builder.buildBranch(cond_value.reg, then_block, cont_block);

                    builder.switchToBlock(then_block);
                    const then_body = if_stmt.thenBody(ctx.root) orelse
                        return ctx.todo(if_stmt.tree, @src());
                    try ctx.genBlock(gen, scope, then_body, builder);
                }

                try builder.buildJump(cont_block);
                builder.switchToBlock(cont_block);
            },
            .loop => |loop_stmt| {
                const body_block = try builder.addBlock(&.{});
                const cont_block = try builder.addBlock(&.{});
                builder.switchToBlock(body_block);
                const if_body = loop_stmt.body(ctx.root) orelse
                    return ctx.todo(loop_stmt.tree, @src());

                try ctx.genBlock(gen, scope, if_body, builder);
                try builder.buildJump(body_block);

                builder.switchToBlock(cont_block);
            },
            .@"while" => |while_stmt| {
                const while_cond = while_stmt.cond(ctx.root) orelse
                    return ctx.todo(while_stmt.tree, @src());

                const while_body = while_stmt.body(ctx.root) orelse
                    return ctx.todo(while_stmt.tree, @src());

                const loop_block = try builder.addBlock(&.{});
                const body_block = try builder.addBlock(&.{});
                const cont_block = try builder.addBlock(&.{});

                builder.switchToBlock(loop_block);
                const cond_value = try genExpr(ctx, gen, scope, while_cond, builder);
                if (cond_value != .reg) {
                    try ctx.err(while_cond.tree(), "cannot use value", .{});
                    return;
                }

                try builder.buildBranch(cond_value.reg, body_block, cont_block);

                builder.switchToBlock(body_block);
                try ctx.genBlock(gen, scope, while_body, builder);
                try builder.buildJump(loop_block);

                builder.switchToBlock(cont_block);
            },
        }
    }
}

fn genExpr(
    ctx: *Context,
    gen: *Gen,
    scope: *const Scope,
    expr: syntax.ast.Expr,
    builder: *ir.Builder,
) error{OutOfMemory}!GenValue {
    switch (expr) {
        .unary => |un| {
            return ctx.genErr(un.tree, "unknown unary operator", .{});
        },
        .binary => |bin| {
            if (bin.plus(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .add);
            if (bin.minus(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .sub);
            if (bin.star(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .mul);
            if (bin.slash(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .div);
            if (bin.percent(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .rem);
            if (bin.lt2(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .shl);
            if (bin.gt2(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .shr);
            if (bin.ampersand(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .band);
            if (bin.pipe(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .bor);
            if (bin.caret(ctx.root) != null) return genArith(ctx, gen, scope, bin, builder, .bxor);
            if (bin.eq2(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .eq);
            if (bin.bangEq(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .neq);
            if (bin.lt(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .lt);
            if (bin.ltEq(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .lte);
            if (bin.gt(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .gt);
            if (bin.gtEq(ctx.root) != null) return genCmp(ctx, gen, scope, bin, builder, .gte);
            return ctx.genErr(bin.tree, "unknown binary operator", .{});
        },
        .literal => |literal| {
            if (literal.number(ctx.root)) |number| {
                const text = ctx.root.tokenText(number);
                const num = std.fmt.parseInt(u64, text, 10) catch |e| {
                    return ctx.genErr(literal.tree, "invalid number literal: {}", .{e});
                };
                return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = num }) };
            }

            return ctx.genErr(literal.tree, "unknown literal", .{});
        },
        .paren => |paren| {
            const inner = paren.expr(ctx.root) orelse
                return ctx.genTodo(paren.tree, @src());

            return genExpr(ctx, gen, scope, inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse
                return ctx.genTodo(call.tree, @src());

            const ident = syntax.ast.Expr.Ident.cast(ctx.root, inner.tree()) orelse
                return ctx.genErr(call.tree, "cannot call non-literal", .{});

            const name = ctx.root.tokenText(ident.ident(ctx.root) orelse
                return ctx.genTodo(call.tree, @src()));

            const lookup_result = scope.get(name) orelse
                return ctx.genTodo(call.tree, @src());

            const decl_syntax = switch (lookup_result) {
                .decl => |decl| decl,
                else => return ctx.genTodo(call.tree, @src()),
            };

            const fn_syntax = syntax.ast.Decl.Fn.cast(ctx.root, decl_syntax.tree()) orelse
                return ctx.genTodo(call.tree, @src());

            const function_ty = try ctx.lookUpType(.{ .function = fn_syntax });
            const function = ctx.fnPtr(ctx.typePtr(function_ty).function);
            const dname = try builder.allocator.dupe(u8, name);

            var params: std.ArrayListUnmanaged(ir.Type) = .{};
            try params.ensureTotalCapacity(builder.allocator, function.params.entries.len);
            defer params.deinit(builder.allocator);

            for (function.params.values()) |param|
                params.appendAssumeCapacity(irType(ctx, param.ty));

            var returns: std.ArrayListUnmanaged(ir.Type) = .{};
            try returns.ensureTotalCapacity(builder.allocator, function.returns.entries.len);
            defer returns.deinit(builder.allocator);

            for (function.returns.values()) |ret|
                returns.appendAssumeCapacity(irType(ctx, ret.ty));

            const extern_func = try builder.declareExternFunc(
                dname,
                try params.toOwnedSlice(builder.allocator),
                try returns.toOwnedSlice(builder.allocator),
            );

            var arg_regs: std.ArrayListUnmanaged(ir.Reg) = .{};
            try arg_regs.ensureTotalCapacity(ctx.gpa, params.items.len);
            defer arg_regs.deinit(ctx.gpa);

            {
                const args = call.args(ctx.root) orelse
                    return ctx.genTodo(function.syntax.tree, @src());
                var it = args.args(ctx.root);
                while (it.next(ctx.root)) |arg_syntax| {
                    const arg_expr = arg_syntax.expr(ctx.root) orelse
                        return ctx.genTodo(function.syntax.tree, @src());
                    const arg_reg = try genExpr(ctx, gen, scope, arg_expr, builder);
                    try arg_regs.append(ctx.gpa, arg_reg.reg);
                }
            }

            const return_regs = try builder.buildCall(extern_func, arg_regs.items);
            return switch (return_regs.len) {
                0 => .void,
                1 => .{ .reg = return_regs[0] },
                else => std.debug.panic("TODO: {}", .{return_regs.len}),
            };
        },
        .ident => |ident| {
            const inner = ident.ident(ctx.root) orelse
                return ctx.genTodo(ident.tree, @src());

            const lookup_result = scope.get(ctx.root.tokenText(inner)) orelse
                return ctx.genErr(ident.tree, "undefined identifier", .{});

            switch (lookup_result) {
                .decl => return ctx.genTodo(ident.tree, @src()),
                .fn_param => |fn_param| {
                    if (gen.vars.get(fn_param.tree)) |reg|
                        return .{ .reg = reg };
                    return ctx.genTodo(ident.tree, @src());
                },
                .true, .false => {
                    return .{
                        .reg = try builder.buildConstant(.i64, ir.Value{
                            .bits = @intFromBool(lookup_result == .true),
                        }),
                    };
                },
                .null => {
                    return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = 0 }) };
                },
            }
        },
    }
}

fn genArith(
    ctx: *Context,
    gen: *Gen,
    scope: *const Scope,
    expr: syntax.ast.Expr.Binary,
    builder: *ir.Builder,
    op: ir.ArithOp,
) error{OutOfMemory}!GenValue {
    const lhs = expr.lhs(ctx.root) orelse
        return ctx.genTodo(expr.tree, @src());
    const lhs_value = try genExpr(ctx, gen, scope, lhs, builder);

    const rhs = expr.rhs(ctx.root) orelse
        return ctx.genTodo(expr.tree, @src());
    const rhs_value = try genExpr(ctx, gen, scope, rhs, builder);

    if (lhs_value != .reg or rhs_value != .reg) {
        if (lhs_value == .void or rhs_value == .void)
            try ctx.err(expr.tree, "cannot use void value", .{});
        return .invalid;
    }

    return .{ .reg = try builder.buildArith(op, lhs_value.reg, rhs_value.reg) };
}

fn genCmp(
    ctx: *Context,
    gen: *Gen,
    scope: *const Scope,
    expr: syntax.ast.Expr.Binary,
    builder: *ir.Builder,
    op: ir.CmpOp,
) error{OutOfMemory}!GenValue {
    const lhs = expr.lhs(ctx.root) orelse
        return ctx.genTodo(expr.tree, @src());

    const rhs = expr.rhs(ctx.root) orelse
        return ctx.genTodo(expr.tree, @src());

    const lhs_value = try genExpr(ctx, gen, scope, lhs, builder);
    const rhs_value = try genExpr(ctx, gen, scope, rhs, builder);

    if (lhs_value != .reg or rhs_value != .reg) {
        if (lhs_value == .void or rhs_value == .void)
            try ctx.err(expr.tree, "cannot use void value", .{});
        return .invalid;
    }

    return .{ .reg = try builder.buildCmp(op, lhs_value.reg, rhs_value.reg) };
}

fn irType(ctx: *Context, type_index: Type.Index) ir.Type {
    const ty = ctx.typePtr(type_index);
    return switch (ty.*) {
        .invalid => .invalid,
        .bool => .i64,
        .unsigned_integer => .i64,
        .pointer => .ptr,
        .structure => .invalid,
        .function => .invalid,
    };
}
