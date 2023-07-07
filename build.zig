const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const syntax = b.addModule("syntax", .{
        .source_file = .{ .path = "lib/syntax.zig" },
    });

    const parse = b.addModule("parse", .{
        .source_file = .{ .path = "lib/parse.zig" },
        .dependencies = &.{
            .{ .name = "syntax", .module = syntax },
        },
    });

    const exe = b.addExecutable(.{
        .name = "compiler",
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });

    exe.addModule("syntax", syntax);
    exe.addModule("parse", parse);

    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args|
        run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);

    const exe_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&exe_tests.step);
}
