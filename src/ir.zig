const std = @import("std");

pub const Reg = struct {
    index: u32,

    pub fn format(reg: Reg, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        if (fmt.len != 0) @compileError("format string should be empty");

        try writer.print("r{}", .{reg.index});
    }
};

pub const BlockRef = struct {
    index: u32,
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
    ret: struct { operand: Reg },
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

        try writer.print("func(", .{});
        for (func.params.items) |param| {
            try writer.print("{}", .{param});
        }
        try writer.print(")", .{});

        if (func.returns.items.len != 0) {
            try writer.print(" (", .{});
            for (func.returns.items) |ret| {
                try writer.print("{}", .{ret});
            }
            try writer.print(")", .{});
        }

        try writer.print(" {{\n", .{});

        for (func.blocks.items, 0..) |block, i| {
            try writer.print("b{}", .{i});
            if (block.params.items.len > 0) {
                try writer.print("(", .{});
                for (block.params.items) |param| {
                    try writer.print("{}", .{param});
                }
                try writer.print(")", .{});
            }
            try writer.print(":", .{});

            for (block.insts.items) |inst| {
                try writer.print("\n    ", .{});
                switch (inst) {
                    // bad
                    .constant => try writer.print("{} = constant {}, {}", .{ inst.constant.dst, inst.constant.type, inst.constant.value }),
                    .param => try writer.print("{} = param {}", .{ inst.param.dst, inst.param.index }),
                    .add => try writer.print("{} = add {}, {}", .{ inst.add.dst, inst.add.lhs, inst.add.rhs }),
                    .ret => try writer.print("ret {}", .{inst.ret.operand}),
                    .unreach => try writer.print("unreach", .{}),
                }
            }
        }

        try writer.print("\n}}", .{});
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

    pub fn buildAdd(builder: *Builder, lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .add = .{ .lhs = lhs, .rhs = rhs, .dst = dst } },
        );
        return dst;
    }

    pub fn buildRet(builder: *Builder, operand: Reg) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[builder.cur_block.index];
        try block.insts.append(
            builder.allocator,
            .{ .ret = .{ .operand = operand } },
        );
    }
};
