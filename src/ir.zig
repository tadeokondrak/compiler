const std = @import("std");

pub const Reg = struct {
    index: u32,

    pub fn format(reg: Reg, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        try writer.print("%{}", .{reg.index});
    }
};

pub const BlockRef = struct {
    index: u32,

    pub fn format(block: BlockRef, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        try writer.print("b{}", .{block.index});
    }
};

pub const Value = struct {
    bits: u64,

    pub fn format(value: Value, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        try writer.print("{}", .{value.bits});
    }
};

pub const Type = enum {
    i32,
    i64,
    ptr,

    pub fn format(@"type": Type, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        switch (@"type") {
            .i32 => try writer.print("i32", .{}),
            .i64 => try writer.print("i64", .{}),
            .ptr => try writer.print("ptr", .{}),
        }
    }
};

pub const Inst = union(enum) {
    constant: struct { type: Type, value: Value, dst: Reg },
    param: struct { dst: Reg, index: u32 },
    add: struct { lhs: Reg, rhs: Reg, dst: Reg },
    sub: struct { lhs: Reg, rhs: Reg, dst: Reg },
    mul: struct { lhs: Reg, rhs: Reg, dst: Reg },
    div: struct { lhs: Reg, rhs: Reg, dst: Reg },
    rem: struct { lhs: Reg, rhs: Reg, dst: Reg },
    lt_eq: struct { lhs: Reg, rhs: Reg, dst: Reg },
    ret_void,
    ret_val: struct { operand: Reg },
    jump: struct { block: BlockRef },
    branch: struct { cond: Reg, then_block: BlockRef, else_block: BlockRef },
    unreach,
};

pub const Func = struct {
    params: std.ArrayListUnmanaged(Type) = .{},
    returns: std.ArrayListUnmanaged(Type) = .{},
    blocks: std.ArrayListUnmanaged(Block) = .{},

    pub fn deinit(func: *Func, allocator: std.mem.Allocator) void {
        func.params.deinit(allocator);
        func.returns.deinit(allocator);
        for (func.blocks.items) |*block| {
            block.params.deinit(allocator);
            block.insts.deinit(allocator);
        }
        func.blocks.deinit(allocator);
    }

    pub fn format(func: Func, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        if (func.params.items.len != 0) {
            try writer.print("params (", .{});
            for (func.params.items) |param| {
                try writer.print("{}", .{param});
            }
            try writer.print(")\n", .{});
        }

        if (func.returns.items.len != 0) {
            try writer.print("returns (", .{});
            for (func.returns.items) |ret| {
                try writer.print("{}", .{ret});
            }
            try writer.print(")\n", .{});
        }

        for (func.blocks.items, 0..) |block, i| {
            try writer.print("b{}", .{i});
            if (block.params.items.len > 0) {
                try writer.print("(", .{});
                for (block.params.items) |param| {
                    try writer.print("{}", .{param});
                }
                try writer.print(")", .{});
            }
            try writer.print(":\n", .{});

            for (block.insts.items) |inst| {
                try writer.print("    {s}", .{@tagName(inst)});
                switch (inst) {
                    inline else => |specific| {
                        if (@TypeOf(specific) == void) continue;
                        inline for (std.meta.fields(@TypeOf(specific)), 0..) |field, j| {
                            if (j > 0) try writer.print(",", .{});
                            try writer.print(" {any}", .{@field(specific, field.name)});
                        }
                    },
                }
                try writer.print("\n", .{});
            }
        }
    }
};

pub const Block = struct {
    params: std.ArrayListUnmanaged(Type) = .{},
    insts: std.ArrayListUnmanaged(Inst) = .{},
};

pub const Builder = struct {
    allocator: std.mem.Allocator,
    func: Func = .{},
    cur_block: BlockRef = .{ .index = ~@as(u32, 0) },
    next_reg: u32 = 0,

    pub fn addReg(builder: *Builder) Reg {
        const reg = builder.next_reg;
        builder.next_reg += 1;
        return .{ .index = reg };
    }

    pub fn addBlock(builder: *Builder) error{OutOfMemory}!BlockRef {
        try builder.func.blocks.append(builder.allocator, .{});
        // TODO: remove intCast
        return .{ .index = @intCast(u32, builder.func.blocks.items.len - 1) };
    }

    pub fn switchToBlock(builder: *Builder, block: BlockRef) void {
        builder.cur_block = block;
    }

    pub fn buildConstant(builder: *Builder, @"type": Type, value: Value) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .constant = .{ .type = @"type", .value = value, .dst = dst } },
        );
        return dst;
    }

    pub fn buildArith(builder: *Builder, comptime tag: std.meta.Tag(Inst), lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            @unionInit(Inst, @tagName(tag), .{ .lhs = lhs, .rhs = rhs, .dst = dst }),
        );
        return dst;
    }

    pub fn buildCmp(builder: *Builder, comptime tag: std.meta.Tag(Inst), lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            @unionInit(Inst, @tagName(tag), .{ .lhs = lhs, .rhs = rhs, .dst = dst }),
        );
        return dst;
    }

    pub fn buildRetVoid(builder: *Builder) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        try block.insts.append(builder.allocator, .ret_void);
    }

    pub fn buildRetVal(builder: *Builder, operand: Reg) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        try block.insts.append(
            builder.allocator,
            .{ .ret_val = .{ .operand = operand } },
        );
    }

    pub fn buildJump(builder: *Builder, to_block: BlockRef) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        try block.insts.append(
            builder.allocator,
            .{ .jump = .{ .block = to_block } },
        );
    }

    pub fn buildBranch(builder: *Builder, cond: Reg, then_block: BlockRef, else_block: BlockRef) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        try block.insts.append(
            builder.allocator,
            .{ .branch = .{ .cond = cond, .then_block = then_block, .else_block = else_block } },
        );
    }
};
