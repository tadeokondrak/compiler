const std = @import("std");

pub const Reg = enum(u32) {
    _,

    pub fn format(reg: Reg, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("v{}", .{@intFromEnum(reg)});
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

pub const ArithOp = enum {
    add,
    sub,
    mul,
    div,
    rem,
    shl,
    shr,
    band,
    bor,
    bxor,

    pub fn format(op: ArithOp, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll(@tagName(op));
    }
};

pub const CmpOp = enum {
    eq,
    neq,
    lt,
    lte,
    gt,
    gte,

    pub fn format(op: CmpOp, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll(@tagName(op));
    }
};

pub const Regs = struct {
    index: u32,
    count: u32,
};

pub const Inst = union(enum) {
    load: struct { type: Type, src: Reg, dst: Reg },
    store: struct { src: Reg, dst: Reg },
    local: struct { local: Local.Index, dst: Reg },
    constant: struct { type: Type, value: Value, dst: Reg },
    arith: struct { op: ArithOp, lhs: Reg, rhs: Reg, dst: Reg },
    cmp: struct { op: CmpOp, lhs: Reg, rhs: Reg, dst: Reg },
    ret: struct { regs: Regs },
    jump: struct { block: Block.Index },
    branch: struct { cond: Reg, then_block: Block.Index, else_block: Block.Index },
    unreach,
    call: struct { func: ExternFunc.Index, args: Regs, dsts: Regs },
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
    locals: std.ArrayListUnmanaged(Local) = .{},
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
            for (func.params.items, 0..) |param, i| {
                if (i > 0) try writer.writeAll(", ");
                try writer.print("{}", .{param});
            }
            try writer.print(")\n", .{});
        }

        if (func.returns.items.len != 0) {
            try writer.print("returns (", .{});
            for (func.returns.items, 0..) |ret, i| {
                if (i > 0) try writer.writeAll(", ");
                try writer.print("{}", .{ret});
            }
            try writer.print(")\n", .{});
        }

        if (func.extern_funcs.items.len != 0) {
            try writer.print("extern_funcs:\n", .{});
            for (func.extern_funcs.items, 0..) |extern_func, i| {
                try writer.print("    {}: {s}(", .{ i, extern_func.name });
                for (extern_func.params, 0..) |param, j| {
                    if (j > 0) try writer.writeAll(", ");
                    try writer.print("{}", .{param});
                }
                try writer.print(") -> (", .{});
                for (extern_func.returns) |ret|
                    try writer.print("{}", .{ret});
                try writer.print(")\n", .{});
            }
        }

        for (func.blocks.items, 0..) |block, i| {
            if (i > 0) try writer.writeByte('\n');
            try writer.print("b{}", .{i});
            if (block.params.len > 0) {
                try writer.print("(", .{});
                for (block.params.items(.reg), block.params.items(.ty), 0..) |reg, ty, j| {
                    if (j > 0) try writer.writeAll(", ");
                    try writer.print("{}: {}", .{ reg, ty });
                }
                try writer.print(")", .{});
            }
            try writer.print(":", .{});

            for (block.insts.items) |inst| {
                try writer.print("\n", .{});
                try writer.writeByteNTimes(' ', 4);

                var printed_lhs = false;
                switch (inst) {
                    inline else => |specific| blk: {
                        if (@TypeOf(specific) == void) break :blk;
                        var first = true;
                        inline for (std.meta.fields(@TypeOf(specific))) |field| {
                            if (!comptime std.mem.startsWith(u8, field.name, "dst"))
                                continue;
                            if (!first) {
                                try writer.print(", ", .{});
                                first = false;
                            }
                            printed_lhs = true;
                            if (field.type == Regs) {
                                const regs = @field(specific, field.name);
                                for (func.extra.items[regs.index..][0..regs.count], 0..) |reg_index, j| {
                                    if (j > 0) try writer.writeAll(", ");
                                    const reg: Reg = @enumFromInt(reg_index);
                                    try writer.print("{any}", .{reg});
                                }
                            } else {
                                try writer.print("{any}", .{@field(specific, field.name)});
                            }
                        }
                    },
                }
                if (printed_lhs) {
                    try writer.print(" = ", .{});
                }
                try writer.print("{s} ", .{@tagName(inst)});
                switch (inst) {
                    inline else => |specific| blk: {
                        if (@TypeOf(specific) == void) break :blk;
                        inline for (std.meta.fields(@TypeOf(specific)), 0..) |field, j| {
                            if (comptime std.mem.startsWith(u8, field.name, "dst"))
                                continue;
                            if (j > 0) try writer.print(", ", .{});
                            if (field.type == Regs) {
                                const regs = @field(specific, field.name);
                                if (regs.count > 1) try writer.writeAll("(");
                                for (func.extra.items[regs.index..][0..regs.count], 0..) |reg_index, k| {
                                    if (k > 0) try writer.writeAll(", ");
                                    const reg: Reg = @enumFromInt(reg_index);
                                    try writer.print("{any}", .{reg});
                                }
                                if (regs.count > 1) try writer.writeAll(")");
                            } else {
                                try writer.print("{any}", .{@field(specific, field.name)});
                            }
                        }
                    },
                }
            }
        }
    }
};

pub const Block = struct {
    params: std.MultiArrayList(Param) = .{},
    insts: std.ArrayListUnmanaged(Inst) = .{},

    pub const Param = struct {
        ty: Type,
        reg: Reg,
    };

    pub const Index = enum(u32) {
        _,

        pub fn format(block: Index, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("b{}", .{@intFromEnum(block)});
        }
    };
};

pub const Local = struct {
    ty: Type,

    pub const Index = enum(u32) {
        _,
    };
};

pub const Builder = struct {
    allocator: std.mem.Allocator,
    func: Func = .{},
    cur_block: Block.Index = @enumFromInt(~@as(u32, 0)),
    next_reg: u32 = 0,

    pub fn addReg(builder: *Builder) Reg {
        const reg = builder.next_reg;
        builder.next_reg += 1;
        return @enumFromInt(reg);
    }

    pub fn addBlock(builder: *Builder, params: []const Block.Param) error{OutOfMemory}!Block.Index {
        const block_ref: u32 = @intCast(builder.func.blocks.items.len);
        const block = try builder.func.blocks.addOne(builder.allocator);
        block.* = .{};
        for (params) |param|
            try block.params.append(builder.allocator, param);
        return @enumFromInt(block_ref);
    }

    pub fn switchToBlock(builder: *Builder, block: Block.Index) void {
        builder.cur_block = block;
    }

    pub fn addLocal(builder: *Builder, ty: Type) !Local.Index {
        builder.func.locals.append(builder.allocator, .{ .ty = ty });
        return @enumFromInt(builder.func.locals.items.len - 1);
    }

    pub fn buildLoad(builder: *Builder, ty: Type, ptr: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .local = .{ .ty = ty, .ptr = ptr, .dst = dst } },
        );
        return dst;
    }

    pub fn buildStore(builder: *Builder, ptr: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .local = .{ .ptr = ptr, .dst = dst } },
        );
        return dst;
    }

    pub fn buildLocal(builder: *Builder, local: Local.Index) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .local = .{ .local = local, .dst = dst } },
        );
        return dst;
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

    pub fn buildArith(builder: *Builder, op: ArithOp, lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .arith = .{ .op = op, .lhs = lhs, .rhs = rhs, .dst = dst } },
        );
        return dst;
    }

    pub fn buildCmp(builder: *Builder, op: CmpOp, lhs: Reg, rhs: Reg) error{OutOfMemory}!Reg {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        const dst = builder.addReg();
        try block.insts.append(
            builder.allocator,
            .{ .cmp = .{ .op = op, .lhs = lhs, .rhs = rhs, .dst = dst } },
        );
        return dst;
    }

    pub fn buildRet(builder: *Builder, values: []const Reg) error{OutOfMemory}!void {
        const reg_extra = builder.func.extra.items.len;
        try builder.func.extra.appendSlice(builder.allocator, @ptrCast(values));
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .ret = .{ .regs = .{ .index = @intCast(reg_extra), .count = @intCast(values.len) } } },
        );
    }

    pub fn buildJump(builder: *Builder, to_block: Block.Index) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .jump = .{ .block = to_block } },
        );
    }

    pub fn buildBranch(builder: *Builder, cond: Reg, then_block: Block.Index, else_block: Block.Index) error{OutOfMemory}!void {
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .branch = .{ .cond = cond, .then_block = then_block, .else_block = else_block } },
        );
    }

    pub fn buildCall(builder: *Builder, func: ExternFunc.Index, args: []const Reg) error{OutOfMemory}![]Reg {
        const extern_func = builder.func.extern_funcs.items[@intFromEnum(func)];
        std.debug.assert(args.len == extern_func.params.len);
        std.debug.assert(extern_func.returns.len == 1);
        const return_count = extern_func.returns.len;
        const arg_extra = builder.func.extra.items.len;
        try builder.func.extra.appendSlice(builder.allocator, @ptrCast(args));
        const dst_extra = builder.func.extra.items.len;
        for (try builder.func.extra.addManyAsSlice(builder.allocator, return_count)) |*return_reg|
            return_reg.* = @intFromEnum(builder.addReg());
        const block = &builder.func.blocks.items[@intFromEnum(builder.cur_block)];
        try block.insts.append(
            builder.allocator,
            .{ .call = .{
                .func = func,
                .args = .{
                    .index = @intCast(arg_extra),
                    .count = @intCast(args.len),
                },
                .dsts = .{
                    .index = @intCast(dst_extra),
                    .count = @intCast(return_count),
                },
            } },
        );
        return @ptrCast(builder.func.extra.items[dst_extra..][0..return_count]);
    }

    pub fn declareExternFunc(builder: *Builder, name: []u8, params: []Type, returns: []Type) error{OutOfMemory}!ExternFunc.Index {
        try builder.func.extern_funcs.append(
            builder.allocator,
            .{ .name = name, .params = params, .returns = returns },
        );
        return @enumFromInt(builder.func.extern_funcs.items.len - 1);
    }
};
