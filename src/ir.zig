const std = @import("std");

pub const Reg = enum(u32) {
    _,

    pub fn format(reg: Reg, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("%{}", .{@intFromEnum(reg)});
    }
};

pub const BlockRef = enum(u32) {
    _,

    pub fn format(block: BlockRef, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("b{}", .{@intFromEnum(block)});
    }
};

pub const Value = struct {
    bits: u64,

    pub fn format(value: Value, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("{}", .{value.bits});
    }
};

pub const Type = enum {
    i64,
    ptr,

    pub fn format(ty: Type, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (ty) {
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
    ret: struct { reg_extra: u32, reg_count: u32 },
    jump: struct { block: BlockRef },
    branch: struct { cond: Reg, then_block: BlockRef, else_block: BlockRef },
    unreach,
    call: struct { func: ExternFunc.Index, arg_extra: u32, arg_count: u32, dst_extra: u32, dst_count: u32 },
};

pub const ExternFunc = struct {
    name: []const u8,
    params: []Type,
    returns: []Type,

    const Index = enum(usize) {
        _,

        pub fn format(index: ExternFunc.Index, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("{}", .{@intFromEnum(index)});
        }
    };

    pub fn deinit(func: *ExternFunc, allocator: std.mem.Allocator) void {
        allocator.free(func.name);
        allocator.free(func.params);
        allocator.free(func.returns);
    }
};

pub const Func = struct {
    params: std.ArrayListUnmanaged(Type) = .{},
    returns: std.ArrayListUnmanaged(Type) = .{},
    blocks: std.ArrayListUnmanaged(Block) = .{},
    extra: std.ArrayListUnmanaged(u32) = .{},
    extern_funcs: std.ArrayListUnmanaged(ExternFunc) = .{},

    pub fn deinit(func: *Func, allocator: std.mem.Allocator) void {
        func.params.deinit(allocator);
        func.returns.deinit(allocator);
        for (func.blocks.items) |*block| {
            block.params.deinit(allocator);
            block.insts.deinit(allocator);
        }
        func.blocks.deinit(allocator);
        func.extra.deinit(allocator);
        for (func.extern_funcs.items) |*extern_func|
            extern_func.deinit(allocator);
        func.extern_funcs.deinit(allocator);
    }

    pub fn format(func: Func, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
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

        if (func.extern_funcs.items.len != 0) {
            try writer.print("extern_funcs:\n", .{});
            for (func.extern_funcs.items, 0..) |extern_func, i| {
                try writer.print("    {}: {s}(", .{ i, extern_func.name });
                for (extern_func.params) |param|
                    try writer.print("{}", .{param});
                try writer.print(") -> (", .{});
                for (extern_func.returns) |ret|
                    try writer.print("{}", .{ret});
                try writer.print(")\n", .{});
            }
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
                            if (comptime std.mem.endsWith(u8, field.name, "_count"))
                                continue;
                            if (j > 0) try writer.print(",", .{});
                            if (comptime std.mem.endsWith(u8, field.name, "_extra")) {
                                const extra = func.extra.items[@field(specific, field.name)..][0..@field(specific, field.name[0 .. field.name.len - 5] ++ "count")];
                                try writer.print(" {any}", .{extra});
                            } else {
                                try writer.print(" {any}", .{@field(specific, field.name)});
                            }
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
    cur_block: BlockRef = @enumFromInt(~@as(u32, 0)),
    next_reg: u32 = 0,

    pub fn addReg(builder: *Builder) Reg {
        const reg = builder.next_reg;
        builder.next_reg += 1;
        return @enumFromInt(reg);
    }

    pub fn addBlock(builder: *Builder) error{OutOfMemory}!BlockRef {
        const block: u32 = @intCast(builder.func.blocks.items.len);
        try builder.func.blocks.append(builder.allocator, .{});
        return @enumFromInt(block);
    }

    pub fn switchToBlock(builder: *Builder, block: BlockRef) void {
        builder.cur_block = block;
    }

    pub fn buildConstant(builder: *Builder, ty: Type, value: Value) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .constant = .{ .type = ty, .value = value, .dst = dst } },
        );
        return dst;
    }

    pub fn buildArith(builder: *Builder, comptime tag: std.meta.Tag(Inst), lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            @unionInit(Inst, @tagName(tag), .{ .lhs = lhs, .rhs = rhs, .dst = dst }),
        );
        return dst;
    }

    pub fn buildCmp(builder: *Builder, comptime tag: std.meta.Tag(Inst), lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            @unionInit(Inst, @tagName(tag), .{ .lhs = lhs, .rhs = rhs, .dst = dst }),
        );
        return dst;
    }

    pub fn buildRet(builder: *Builder, values: []const Reg) error{OutOfMemory}!void {
        const reg_extra = builder.func.extra.items.len;
        try builder.func.extra.appendSlice(builder.allocator, @ptrCast(values));
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .ret = .{ .reg_extra = @intCast(reg_extra), .reg_count = @intCast(values.len) } },
        );
    }

    pub fn buildJump(builder: *Builder, to_block: BlockRef) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .jump = .{ .block = to_block } },
        );
    }

    pub fn buildBranch(builder: *Builder, cond: Reg, then_block: BlockRef, else_block: BlockRef) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .branch = .{ .cond = cond, .then_block = then_block, .else_block = else_block } },
        );
    }

    pub fn buildCall(builder: *Builder, func: ExternFunc.Index, args: []const Reg) error{OutOfMemory}![]Reg {
        const extern_func = builder.func.extern_funcs.items[@intFromEnum(func)];
        std.debug.assert(args.len == extern_func.params.len);
        const return_count = extern_func.returns.len;
        const arg_extra = builder.func.extra.items.len;
        try builder.func.extra.appendSlice(builder.allocator, @ptrCast(args));
        const dst_extra = builder.func.extra.items.len;
        for (try builder.func.extra.addManyAsSlice(builder.allocator, return_count)) |*return_reg|
            return_reg.* = @intFromEnum(builder.addReg());
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{
                .call = .{
                    .func = func,
                    .arg_extra = @intCast(arg_extra),
                    .arg_count = @intCast(args.len),
                    .dst_extra = @intCast(dst_extra),
                    .dst_count = @intCast(return_count),
                },
            },
        );
        return @ptrCast(builder.func.extra.items[arg_extra..][0..args.len]);
    }

    pub fn declareExternFunc(builder: *Builder, name: []u8, params: []Type, returns: []Type) error{OutOfMemory}!ExternFunc.Index {
        try builder.func.extern_funcs.append(
            builder.allocator,
            .{ .name = name, .params = params, .returns = returns },
        );
        return @enumFromInt(builder.func.extern_funcs.items.len - 1);
    }
};
