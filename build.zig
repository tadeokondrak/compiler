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

    const ungrammar = b.addModule("ungrammar", .{
        .source_file = .{ .path = "lib/ungrammar/ungrammar.zig" },
    });

    const ungrammar2json = b.addExecutable(.{
        .name = "ungrammar2json",
        .root_source_file = .{ .path = "cmd/ungrammar2json/ungrammar2json.zig" },
        .target = target,
        .optimize = optimize,
    });

    ungrammar2json.addModule("ungrammar", ungrammar);

    b.installArtifact(ungrammar2json);

    const ast_codegen = b.addExecutable(.{
        .name = "ast-codegen",
        .root_source_file = .{ .path = "cmd/ast/ast.zig" },
    });

    ast_codegen.addModule("ungrammar", ungrammar);

    const run_ast_codegen = b.addRunArtifact(ast_codegen);
    run_ast_codegen.addFileSourceArg(.{ .path = "ast.ungram" });
    const generated_ast_zig = run_ast_codegen.addOutputFileArg("ast.zig");

    b.installArtifact(ast_codegen);

    const ast = b.addModule("ast", .{
        .source_file = generated_ast_zig,
        .dependencies = &.{
            .{ .name = "syntax", .module = syntax },
        },
    });

    const sema = b.addModule("sema", .{
        .source_file = .{ .path = "lib/sema.zig" },
        .dependencies = &.{
            .{ .name = "syntax", .module = syntax },
            .{ .name = "parse", .module = parse },
            .{ .name = "ast", .module = ast },
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
    exe.addModule("sema", sema);
    exe.addModule("ast", ast);

    b.installArtifact(exe);

    const lsp = b.addExecutable(.{
        .name = "lsp",
        .root_source_file = .{ .path = "cmd/lsp/main.zig" },
        .target = target,
        .optimize = optimize,
    });

    lsp.addModule("syntax", syntax);
    lsp.addModule("parse", parse);
    lsp.addModule("sema", sema);
    lsp.addModule("ast", ast);
    lsp.addModule("zig-lsp", b.dependency("zig-lsp", .{}).module("zig-lsp"));

    b.installArtifact(lsp);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(&exe.step);
    const run_step = b.step("run", "Run the compiler");
    run_step.dependOn(&run_cmd.step);

    const lsp_step = b.step("lsp", "Build the language server");
    lsp_step.dependOn(&lsp.step);

    const exe_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/tests.zig" },
        .target = target,
        .optimize = optimize,
    });
    exe_tests.addModule("syntax", syntax);
    exe_tests.addModule("parse", parse);
    exe_tests.addModule("sema", sema);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&exe_tests.step);
}
