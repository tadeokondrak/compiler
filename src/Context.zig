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
types: std.ArrayListUnmanaged(Type) = .{},
structs: std.ArrayListUnmanaged(Struct) = .{},

const TypeKey = union(enum) {
    invalid,
    integer: struct { bits: u32 },
    structure: ast.Decl.Struct,
};

const Type = union(enum) {
    const Index = struct { index: usize };

    invalid,
    integer: struct { bits: u32 },
    structure: Struct,

    fn deinit(typ: *Type, allocator: std.mem.Allocator) void {
        switch (typ.*) {
            .invalid, .integer => {},
            .structure => {
                typ.structure.fields.deinit(allocator);
            },
        }
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

fn typeMatchesKey(typ: Type, key: TypeKey) bool {
    return switch (typ) {
        .invalid => key == .invalid,
        .integer => |integer_type| key == .integer and key.integer.bits == integer_type.bits,
        .structure => |struct_type| key == .structure and key.structure.tree.index == struct_type.decl.tree.index,
    };
}

// TODO: infer or make a global error thing
fn getTypeByKey(ctx: *Context, key: TypeKey) error{ OutOfMemory, MissingStructName, ExpectedStructField, MissingStructFieldName, MissingStructFieldType, TODO }!Type.Index {
    for (ctx.types.items, 0..) |typ, i| {
        if (typeMatchesKey(typ, key))
            return Type.Index{ .index = i };
    }

    switch (key) {
        .invalid => {
            try ctx.types.append(ctx.allocator, .invalid);
            return Type.Index{ .index = ctx.types.items.len - 1 };
        },
        .integer => {
            try ctx.types.append(ctx.allocator, .{ .integer = .{ .bits = key.integer.bits } });
            return Type.Index{ .index = ctx.types.items.len - 1 };
        },
        .structure => |struct_key| {
            const struct_ident = struct_key.ident(ctx.root) orelse return error.MissingStructName;
            const struct_name = ctx.root.tokenText(struct_ident);
            const struct_type = try ctx.types.addOne(ctx.allocator);
            struct_type.* = .{
                .structure = .{
                    .decl = struct_key,
                    .name = struct_name,
                },
            };

            for (ctx.root.treeChildren(struct_key.tree)) |child| {
                if (child.asTree()) |child_tree| {
                    const field = ast.Decl.Struct.Field.cast(ctx.root, child_tree) orelse return error.ExpectedStructField;
                    const name = field.ident(ctx.root) orelse return error.MissingStructFieldName;
                    const name_text = ctx.root.tokenText(name);
                    const type_expr = field.typeExpr(ctx.root) orelse return error.MissingStructFieldType;
                    const field_type = try ctx.analyzeTypeExpr(type_expr);
                    try struct_type.structure.fields.append(ctx.allocator, .{
                        .name = name_text,
                        .type = field_type,
                    });
                }
            }

            return Type.Index{ .index = ctx.types.items.len - 1 };
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
    for (ctx.types.items) |*typ| typ.deinit(ctx.allocator);
    ctx.types.deinit(ctx.allocator);
    ctx.root.deinit(ctx.allocator);
}

pub fn analyzeDecls(ctx: *Context) !void {
    var it = ctx.file.decls(ctx.root);
    while (it.next(ctx.root)) |decl| {
        switch (decl) {
            .function => |function| try ctx.analyzeFunction(function),
            .structure => |structure| {
                _ = try ctx.getTypeByKey(.{ .structure = structure });
            },
        }
    }
}

fn analyzeFunction(ctx: *Context, function: ast.Decl.Fn) !void {
    var builder = ir.Builder{ .allocator = ctx.allocator };
    defer builder.func.deinit(ctx.allocator);
    const name = function.ident(ctx.root) orelse return error.MissingFunctionName;
    const name_text = ctx.root.tokenText(name);
    const block = function.body(ctx.root) orelse return error.MissingFunctionBody;
    builder.switchToBlock(try builder.addBlock());
    try ctx.genBlock(block, &builder);
    std.debug.print("{s}: {}\n", .{ name_text, builder.func });
}

fn analyzeTypeExpr(ctx: *Context, type_expr: ast.TypeExpr) !Type.Index {
    switch (type_expr) {
        .ident => |ident| {
            const ident_token = ident.ident(ctx.root) orelse return error.MissingStructFieldType;
            const ident_text = ctx.root.tokenText(ident_token);
            if (std.mem.eql(u8, ident_text, "u32")) {
                return ctx.getTypeByKey(.{ .integer = .{ .bits = 32 } });
            }

            return error.TODO;
        },
    }
}

fn genBlock(ctx: *Context, block: ast.Stmt.Block, builder: *ir.Builder) !void {
    for (ctx.root.treeChildren(block.tree)) |child| {
        if (child.asTree()) |child_tree| {
            const stmt = ast.Stmt.cast(ctx.root, child_tree) orelse return error.ExpectedStatement;
            switch (stmt) {
                .expr => |expr_stmt| {
                    const expr = expr_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
                    _ = try ctx.genExpr(expr, builder);
                },
                .block => |nested_block| {
                    return ctx.genBlock(nested_block, builder);
                },
                .@"return" => |return_stmt| {
                    const expr = return_stmt.expr(ctx.root) orelse return error.ExpectedExpression;
                    const value = try ctx.genExpr(expr, builder) orelse return error.ExpectedReturnValue;
                    try builder.buildRet(value.reg);
                },
            }
        }
    }
}

fn genExpr(ctx: *Context, expr: ast.Expr, builder: *ir.Builder) !?Value {
    switch (expr) {
        .unary => |unary| {
            _ = unary;
            return error.UnknownUnop;
        },
        .binary => |binary| {
            if (binary.plus(ctx.root)) |_| {
                const lhs = binary.lhs(ctx.root) orelse return error.ExpectedExpression;
                const rhs = binary.rhs(ctx.root) orelse return error.ExpectedExpression;
                const lhs_value = try ctx.genExpr(lhs, builder) orelse return error.ExpectedValue;
                const rhs_value = try ctx.genExpr(rhs, builder) orelse return error.ExpectedValue;

                return .{ .reg = try builder.buildAdd(lhs_value.reg, rhs_value.reg) };
            }

            return error.UnknownBinop;
        },
        .literal => |literal| {
            if (literal.number(ctx.root)) |number| {
                const text = ctx.root.tokenText(number);
                const num = try std.fmt.parseInt(u64, text, 10);
                return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = num }) };
            }

            return error.UnknownLiteral;
        },
        .paren => |paren| {
            const inner = paren.expr(ctx.root) orelse return error.ExpectedExpression;
            return ctx.genExpr(inner, builder);
        },
        .call => |call| {
            const inner = call.expr(ctx.root) orelse return error.ExpectedExpression;
            // TODO
            return ctx.genExpr(inner, builder);
        },
        .ident => |ident| {
            _ = ident;
            return .{ .reg = try builder.buildConstant(.i64, ir.Value{ .bits = 0 }) };
        },
    }
}
