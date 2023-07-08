const std = @import("std");

pub fn Db(
    comptime InputStateT: type,
    comptime input_queries_t: type,
    comptime derived_queries_t: type,
) type {
    return struct {
        allocator: std.mem.Allocator,
        generation: u64 = 0,
        input_state: InputState,
        input_query_storage: InputQueryStorage = .{},
        derived_query_storage: DerivedQueryStorage = .{},
        context_stack: std.ArrayListUnmanaged(Context) = .{},

        pub fn deinit(db: *Self) void {
            db.context_stack.deinit(db.allocator);
            inline for (comptime std.meta.declarations(input_queries)) |decl| {
                const storage = &@field(db.input_query_storage, decl.name);
                storage.deinit(db.allocator);
            }
            inline for (comptime std.meta.declarations(derived_queries)) |decl| {
                const storage = &@field(db.derived_query_storage, decl.name);
                for (storage.values()) |value|
                    db.allocator.free(value.dependencies);
                storage.deinit(db.allocator);
            }
        }

        const Self = @This();

        pub const InputState = InputStateT;
        pub const input_queries = input_queries_t;
        pub const derived_queries = derived_queries_t;

        const Context = struct {
            dependencies: std.ArrayListUnmanaged(Dependency) = .{},
        };

        const Dependency = struct {
            tag: QueryTag,
            input: u64,
        };

        const QueryTag = @Type(.{
            .Enum = .{
                .tag_type = u16,
                .fields = fields: {
                    const input_query_decls = std.meta.declarations(input_queries);
                    const derived_query_decls = std.meta.declarations(derived_queries);

                    comptime var fields: [input_query_decls.len + derived_query_decls.len]std.builtin.Type.EnumField = undefined;

                    inline for (input_query_decls, 0..) |decl, i| {
                        fields[i] = .{
                            .name = decl.name,
                            .value = i,
                        };
                    }

                    inline for (derived_query_decls, input_query_decls.len..) |decl, i| {
                        fields[i] = .{
                            .name = decl.name,
                            .value = i,
                        };
                    }

                    break :fields &fields;
                },
                .decls = &.{},
                .is_exhaustive = true,
            },
        });

        const first_derived_query = std.meta.declarations(input_queries).len;

        const InputQueryStorage = @Type(.{
            .Struct = .{
                .layout = .Auto,
                .fields = fields: {
                    comptime var fields: [std.meta.declarations(input_queries).len]std.builtin.Type.StructField = undefined;

                    inline for (std.meta.declarations(input_queries), 0..) |decl, i| {
                        const queryFn = @field(input_queries, decl.name);
                        const query_info = @typeInfo(@TypeOf(queryFn)).Fn;
                        std.debug.assert(query_info.params[0].type == InputState);
                        std.debug.assert(query_info.params.len == 2);
                        const Input = query_info.params[1].type.?;
                        const Result = query_info.return_type.?;
                        const Data = struct {
                            result: Result,
                            last_changed: u64,
                        };
                        const Field = std.AutoArrayHashMapUnmanaged(Input, Data);
                        fields[i] = .{
                            .name = decl.name,
                            .type = Field,
                            .default_value = @as(?*const Field, &Field{}),
                            .is_comptime = false,
                            .alignment = @alignOf(Field),
                        };
                    }

                    break :fields &fields;
                },
                .decls = &.{},
                .is_tuple = false,
            },
        });

        const DerivedQueryStorage = @Type(.{
            .Struct = .{
                .layout = .Auto,
                .fields = fields: {
                    comptime var fields: [std.meta.declarations(derived_queries).len]std.builtin.Type.StructField = undefined;

                    inline for (std.meta.declarations(derived_queries), 0..) |decl, i| {
                        const queryFn = @field(derived_queries, decl.name);
                        const query_info = @typeInfo(@TypeOf(queryFn)).Fn;
                        std.debug.assert(query_info.params.len == 2);
                        const Input = query_info.params[1].type.?;
                        const Result = query_info.return_type.?;
                        const Data = struct {
                            result: Result,
                            last_changed: u64,
                            last_checked: u64,
                            dependencies: []Dependency,
                        };
                        const Field = std.AutoArrayHashMapUnmanaged(Input, Data);
                        fields[i] = .{
                            .name = decl.name,
                            .type = Field,
                            .default_value = @as(?*const Field, &Field{}),
                            .is_comptime = false,
                            .alignment = @alignOf(Field),
                        };
                    }

                    break :fields &fields;
                },
                .decls = &.{},
                .is_tuple = false,
            },
        });

        fn QueryInput(comptime tag: QueryTag) type {
            const query_index: u32 = @intFromEnum(tag);
            const Field = @TypeOf(
                @field(
                    if (query_index < first_derived_query)
                        input_queries
                    else
                        derived_queries,
                    @tagName(tag),
                ),
            );
            return @typeInfo(Field).Fn.params[1].type.?;
        }

        fn QueryResult(comptime tag: QueryTag) type {
            const query_index: u32 = @intFromEnum(tag);
            const Field = @TypeOf(
                @field(
                    if (query_index < first_derived_query)
                        input_queries
                    else
                        derived_queries,
                    @tagName(tag),
                ),
            );
            const Return = @typeInfo(Field).Fn.return_type.?;
            return @typeInfo(Return).ErrorUnion.payload;
        }

        fn packInput(comptime tag: QueryTag, input: QueryInput(tag)) u64 {
            return switch (QueryInput(tag)) {
                void => 0,
                u32, u64 => input,
                usize => input,
                else => @panic("TODO"),
            };
        }

        fn unpackInput(comptime tag: QueryTag, input: u64) QueryInput(tag) {
            return switch (QueryInput(tag)) {
                void => {},
                u32 => @truncate(input),
                u64 => input,
                usize => @truncate(input),
                else => @panic("TODO"),
            };
        }

        pub fn query(db: *Self, comptime tag: QueryTag, input: QueryInput(tag)) error{OutOfMemory}!QueryResult(tag) {
            if (db.context_stack.items.len > 0) {
                const last = &db.context_stack.items[db.context_stack.items.len - 1];
                try last.dependencies.append(db.allocator, .{
                    .tag = tag,
                    .input = packInput(tag, input),
                });
            }

            const query_index: u32 = @intFromEnum(tag);
            return if (query_index < first_derived_query)
                db.queryInput(tag, input)
            else
                db.queryDerived(tag, input);
        }

        inline fn queryInput(db: *Self, comptime tag: QueryTag, input: QueryInput(tag)) error{OutOfMemory}!QueryResult(tag) {
            const storage = &@field(db.input_query_storage, @tagName(tag));
            const entry = try storage.getOrPut(db.allocator, input);
            const data = entry.value_ptr;
            if (entry.found_existing and db.generation == data.last_changed)
                return data.result;

            const computed = @field(input_queries, @tagName(tag))(db.input_state, input);
            if (!entry.found_existing or !std.meta.eql(data.result, computed)) {
                data.result = computed;
                data.last_changed = db.generation;
            }

            return data.result;
        }

        inline fn queryDerived(db: *Self, comptime tag: QueryTag, input: QueryInput(tag)) error{OutOfMemory}!QueryResult(tag) {
            const storage = &@field(db.derived_query_storage, @tagName(tag));
            const entry = try storage.getOrPut(db.allocator, input);
            const data = entry.value_ptr;
            if (entry.found_existing and db.generation == data.last_checked) {
                return data.result;
            }

            data.last_checked = db.generation;

            var any_dependency_changed = !entry.found_existing or blk: {
                for (data.dependencies) |dependency| {
                    switch (dependency.tag) {
                        inline else => |dependency_tag| {
                            if (try db.maybeChangedSince(
                                dependency_tag,
                                unpackInput(dependency_tag, dependency.input),
                                data.last_changed,
                            )) {
                                break :blk true;
                            }
                        },
                    }
                }
                break :blk false;
            };

            if (any_dependency_changed) {
                const context = try db.context_stack.addOne(db.allocator);
                defer _ = db.context_stack.pop();
                defer context.dependencies.deinit(db.allocator);

                context.* = .{};

                const computed = @field(derived_queries, @tagName(tag))(db, input);
                if (!entry.found_existing or !std.meta.eql(data.result, computed)) {
                    if (entry.found_existing) db.allocator.free(data.dependencies);
                    data.* = .{
                        .result = computed,
                        .last_checked = db.generation,
                        .last_changed = db.generation,
                        .dependencies = try context.dependencies.toOwnedSlice(db.allocator),
                    };
                }
            }

            return data.result;
        }

        fn maybeChangedSince(db: *Self, comptime tag: QueryTag, input: QueryInput(tag), revision: u64) error{OutOfMemory}!bool {
            const query_index: u32 = @intFromEnum(tag);
            if (query_index < first_derived_query) {
                const storage = &@field(db.input_query_storage, @tagName(tag));
                return if (storage.contains(input)) db.generation > revision else true;
            }

            const storage = &@field(db.derived_query_storage, @tagName(tag));
            const data = storage.getPtr(input) orelse return true;

            if (db.generation == data.last_checked)
                return data.last_changed > revision;

            for (data.dependencies) |dependency| {
                switch (dependency.tag) {
                    inline else => |dependency_tag| {
                        if (try db.maybeChangedSince(
                            dependency_tag,
                            unpackInput(dependency_tag, dependency.input),
                            revision,
                        )) {
                            return true;
                        }
                    },
                }
            }

            return false;
        }
    };
}

const tests = struct {
    const DbT = Db(State, input_queries, derived_queries);

    const State = struct {
        source_text: []const u8,
    };

    const input_queries = struct {
        fn source_text(state: State, _: void) ![]const u8 {
            std.debug.print("!! input_queries.source_text\n", .{});
            return state.source_text;
        }
    };

    const derived_queries = struct {
        fn source_text_len(db: *DbT, _: void) !usize {
            std.debug.print("!! derived_queries.source_text_len\n", .{});
            return (try db.query(.source_text, {})).len;
        }

        fn source_text_len_plus_one(db: *DbT, _: void) !usize {
            std.debug.print("!! derived_queries.source_text_len_plus_one\n", .{});
            return (try db.query(.source_text_len, {})) + 1;
        }

        fn source_text_len_plus_n(db: *DbT, n: usize) !usize {
            std.debug.print("!! derived_queries.source_text_len_plus_n {}\n", .{n});
            return (try db.query(.source_text_len, {})) + n;
        }
    };
};

test Db {
    var db = tests.DbT{
        .allocator = std.testing.allocator,
        .input_state = .{
            .source_text = "hello world",
        },
    };
    defer db.deinit();

    std.debug.print("---\n", .{});
    try std.testing.expectEqualStrings("hello world", try db.query(.source_text, {}));
    try std.testing.expectEqual("hello world".len, try db.query(.source_text_len, {}));
    try std.testing.expectEqual("hello world".len + 1, try db.query(.source_text_len_plus_one, {}));
    try std.testing.expectEqual("hello world".len + 2, try db.query(.source_text_len_plus_n, 2));
    try std.testing.expectEqual("hello world".len + 3, try db.query(.source_text_len_plus_n, 3));

    try std.testing.expectEqualStrings("hello world", try db.query(.source_text, {}));
    try std.testing.expectEqual("hello world".len, try db.query(.source_text_len, {}));
    try std.testing.expectEqual("hello world".len + 1, try db.query(.source_text_len_plus_one, {}));
    try std.testing.expectEqual("hello world".len + 2, try db.query(.source_text_len_plus_n, 2));
    try std.testing.expectEqual("hello world".len + 3, try db.query(.source_text_len_plus_n, 3));

    std.debug.print("---\n", .{});
    db.input_state = .{ .source_text = "world hello" };
    db.generation += 1;

    try std.testing.expectEqualStrings("world hello", try db.query(.source_text, {}));
    try std.testing.expectEqual("world hello".len, try db.query(.source_text_len, {}));
    try std.testing.expectEqual("world hello".len + 1, try db.query(.source_text_len_plus_one, {}));
    try std.testing.expectEqual("world hello".len + 2, try db.query(.source_text_len_plus_n, 2));
    try std.testing.expectEqual("world hello".len + 3, try db.query(.source_text_len_plus_n, 3));

    std.debug.print("---\n", .{});
    db.input_state = .{ .source_text = "hello" };
    db.generation += 1;

    try std.testing.expectEqualStrings("hello", try db.query(.source_text, {}));
    try std.testing.expectEqual("hello".len, try db.query(.source_text_len, {}));
    try std.testing.expectEqual("hello".len + 1, try db.query(.source_text_len_plus_one, {}));
    try std.testing.expectEqual("hello".len + 2, try db.query(.source_text_len_plus_n, 2));
    try std.testing.expectEqual("hello".len + 3, try db.query(.source_text_len_plus_n, 3));

    std.debug.print("---\n", .{});
    db.input_state = .{ .source_text = "elloh" };
    db.generation += 1;

    try std.testing.expectEqualStrings("elloh", try db.query(.source_text, {}));
    try std.testing.expectEqual("elloh".len, try db.query(.source_text_len, {}));
    try std.testing.expectEqual("elloh".len + 1, try db.query(.source_text_len_plus_one, {}));
    try std.testing.expectEqual("elloh".len + 2, try db.query(.source_text_len_plus_n, 2));
    try std.testing.expectEqual("elloh".len + 3, try db.query(.source_text_len_plus_n, 3));
}
