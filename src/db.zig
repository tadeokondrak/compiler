const std = @import("std");

const State = struct {
    source_text: []const u8,
};

const queries = struct {
    const impure = struct {
        const source_text = struct {
            const Input = void;
            const Output = []const u8;

            fn compute(state: State, _: Input) !Output {
                return state.source_text;
            }
        };
    };

    const pure = struct {
        const source_text_len = struct {
            const Input = void;
            const Output = usize;

            fn compute(db: *Db, _: Input) !Output {
                const text = try db.query(.source_text, {});
                return text.len;
            }
        };

        const source_text_len_plus_one = struct {
            const Input = void;
            const Output = usize;

            fn compute(db: *Db, _: Input) !Output {
                const len = try db.query(.source_text_len, {});
                return len + 1;
            }
        };
    };
};

const Db = struct {
    raw_state: State,
    allocator: std.mem.Allocator,
    generation: u64 = 0,
    storage: @Type(.{ .Struct = .{
        .layout = .Auto,
        .fields = blk: {
            comptime var fields: []const std.builtin.Type.StructField = &.{};
            for (std.meta.declarations(queries.impure)) |decl| {
                const ImpureQ = @field(queries.impure, decl.name);
                const ImpureOutputData = struct {
                    output: ImpureQ.Output,
                    last_changed: u64,
                };
                const ImpureMap = std.AutoHashMapUnmanaged(ImpureQ.Input, ImpureOutputData);
                fields = fields ++ &[_]std.builtin.Type.StructField{.{
                    .name = decl.name,
                    .type = ImpureMap,
                    .default_value = &ImpureMap{},
                    .is_comptime = false,
                    .alignment = @alignOf(ImpureMap),
                }};
            }
            for (std.meta.declarations(queries.pure)) |decl| {
                const PureQ = @field(queries.pure, decl.name);
                const PureOutputData = struct {
                    output: PureQ.Output,
                    last_changed: u64,
                    last_computed: u64,
                    dependencies: []struct { tag: QueryTag, hash: u64 },
                };
                const PureMap = std.AutoHashMapUnmanaged(PureQ.Input, PureOutputData);
                fields = fields ++ &[_]std.builtin.Type.StructField{.{
                    .name = decl.name,
                    .type = PureMap,
                    .default_value = &PureMap{},
                    .is_comptime = false,
                    .alignment = @alignOf(PureMap),
                }};
            }
            break :blk fields;
        },
        .decls = &.{},
        .is_tuple = false,
    } }) = .{},
    context: ?Db.Context = null,

    const Context = struct {
        saw_state: bool,
    };

    const QueryTag = blk: {
        const fieldInfo = std.meta.declarations(queries.impure) ++ std.meta.declarations(queries.pure);
        var enumDecls: [fieldInfo.len]std.builtin.Type.EnumField = undefined;
        var decls = [_]std.builtin.Type.Declaration{};
        inline for (fieldInfo, 0..) |field, i| {
            enumDecls[i] = .{ .name = field.name, .value = i };
        }
        break :blk @Type(.{
            .Enum = .{
                .tag_type = std.math.IntFittingRange(0, fieldInfo.len - 1),
                .fields = &enumDecls,
                .decls = &decls,
                .is_exhaustive = true,
            },
        });
    };

    pub fn Query(comptime tag: QueryTag) type {
        if (@hasDecl(queries.impure, @tagName(tag)))
            return @field(queries.impure, @tagName(tag));
        if (@hasDecl(queries.pure, @tagName(tag)))
            return @field(queries.pure, @tagName(tag));
        unreachable;
    }

    pub fn deinit(db: *Db) void {
        inline for (std.meta.fields(@TypeOf(db.storage))) |field|
            @field(db.storage, field.name).deinit(db.allocator);
    }

    pub fn query(db: *Db, comptime tag: QueryTag, input: Query(tag).Input) error{OutOfMemory}!Query(tag).Output {
        if (@hasDecl(queries.impure, @tagName(tag)))
            return queryImpure(db, tag, input);
        if (@hasDecl(queries.pure, @tagName(tag)))
            return queryPure(db, tag, input);
        unreachable;
    }

    inline fn queryPure(db: *Db, comptime tag: QueryTag, input: Query(tag).Input) Query(tag).Output {
        _ = input;
        _ = db;
        @panic("TODO");
    }

    inline fn queryImpure(db: *Db, comptime tag: QueryTag, input: Query(tag).Input) !Query(tag).Output {
        _ = input;
        _ = db;
        @panic("TODO");

        //        const storage = &@field(db.storage, @tagName(tag));
        //        const result = try storage.getOrPut(db.allocator, input);
        //        const data = result.value_ptr;
        //
        //        @compileLog(tag);
        //
        //        if (result.found_existing and
        //            db.generation == result.value_ptr.last_computed)
        //        {
        //            return data.output;
        //        }
        //
        //        const old_context = db.context;
        //        db.context = .{};
        //        const new_output = try Query(tag).compute(db, input);
        //        const context = db.context;
        //        db.context = old_context;
        //
        //        _ = context;
        //
        //        if (!result.found_existing and std.meta.eql(data.output, new_output)) {
        //            data.last_computed = db.generation;
        //            return data.output;
        //        }
        //
        //        data.* = .{
        //            .output = new_output,
        //            .last_changed = db.generation,
        //            .last_computed = db.generation,
        //            .dependencies = &.{},
        //        };
        //
        //        return data.output;
    }

    pub fn queryAssumePresent(db: *Db, comptime tag: QueryTag, input: Query(tag).Input) Query(tag).Output {
        _ = input;
        _ = db;
        @panic("TODO");
        //        const storage = &@field(db.storage, @tagName(tag));
        //        const data = storage.getPtr(input) orelse unreachable;
        //
        //        if (db.generation == data.last_computed)
        //            return data.output;
        //
        //        unreachable;
    }

    pub fn state(db: *Db) *State {
        return &db.raw_state;
    }

    pub fn setState(db: *Db, new_state: State) void {
        db.raw_state = new_state;
        db.generation += 1;
    }
};

test Db {
    var db = Db{
        .allocator = std.testing.allocator,
        .raw_state = .{
            .source_text = "source text",
        },
    };
    defer db.deinit();

    try std.testing.expectEqualSlices(u8, "source text", try db.query(.source_text, {}));
    //    try std.testing.expectEqual(@as(usize, 11), try db.query(.source_text_len, {}));
    //
    //    db.raw_state.source_text = "other text";
    //
    //    try std.testing.expectEqualSlices(u8, "source text", db.queryAssumePresent(.source_text, {}));
    //    try std.testing.expectEqual(@as(usize, 11), db.queryAssumePresent(.source_text_len, {}));
    //
    //    db.generation += 1;
    //
    //    try std.testing.expectEqualSlices(u8, "other text", try db.query(.source_text, {}));
    //    try std.testing.expectEqual(@as(usize, 10), try db.query(.source_text_len, {}));
    //    try std.testing.expectEqual(@as(usize, 11), try db.query(.source_text_len_plus_one, {}));
    //
    //    try std.testing.expectEqualSlices(u8, "other text", db.queryAssumePresent(.source_text, {}));
    //    try std.testing.expectEqual(@as(usize, 10), db.queryAssumePresent(.source_text_len, {}));
    //    try std.testing.expectEqual(@as(usize, 11), db.queryAssumePresent(.source_text_len_plus_one, {}));
    //
    //    db.setState(.{ .source_text = "text other" });
    //
    //    try std.testing.expectEqualSlices(u8, "text other", try db.query(.source_text, {}));
    //    try std.testing.expectEqual(@as(usize, 10), try db.query(.source_text_len, {}));
    //    try std.testing.expectEqual(@as(usize, 11), db.queryAssumePresent(.source_text_len_plus_one, {}));
}
