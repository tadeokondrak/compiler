const std = @import("std");
const syntax = @import("../syntax.zig");

const ast = @This();

comptime {
    std.testing.refAllDeclsRecursive(ast);
}

pub fn Ptr(comptime T: type) type {
    return struct {
        span: syntax.pure.Span,

        pub fn deref(ptr: @This(), tree: *syntax.Tree) !T {
            const found = try tree.findTree(ptr.span);
            return T.cast(found.?).?;
        }
    };
}

fn AstUnion(comptime This: type) type {
    return struct {
        pub fn cast(syntax_tree: *syntax.Tree) ?This {
            inline for (@typeInfo(This).Union.fields) |field|
                if (field.type.cast(syntax_tree)) |correct_tree|
                    return @unionInit(This, field.name, correct_tree);
            return null;
        }

        pub fn tree(this: This) *syntax.Tree {
            return switch (this) {
                inline else => |variant| variant.tree,
            };
        }

        pub fn ptr(this: This) Ptr(This) {
            return .{ .span = this.span() };
        }

        pub fn span(this: This) syntax.pure.Span {
            return switch (this) {
                inline else => |variant| variant.span(),
            };
        }
    };
}

fn AstTree(
    comptime This: type,
    comptime tag: syntax.pure.Tree.Tag,
) type {
    return struct {
        pub fn ptr(this: This) Ptr(This) {
            return .{ .span = this.tree.span() };
        }

        pub fn span(this: This) syntax.pure.Span {
            return this.tree.span();
        }

        pub fn cast(tree: *syntax.Tree) ?This {
            if (tree.tag != tag) return null;
            return This{ .tree = tree };
        }

        pub fn format(this: This, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(@tagName(tag) ++ "(");
            try writer.print("{}", .{@intFromEnum(this.tree)});
            try writer.writeAll(")");
        }
    };
}

fn AstTreeWithChildren(
    comptime This: type,
    comptime tag: syntax.pure.Tree.Tag,
    comptime Child: type,
) type {
    return struct {
        pub usingnamespace AstTree(This, tag);
        pub fn iter(this: This) error{OutOfMemory}!ast.TreeIterator(Child) {
            return .{ .nodes = try this.tree.children() };
        }
    };
}

fn nthTreeAccessorFn(comptime This: type, comptime Tree: type, comptime nth: usize) fn (This) error{OutOfMemory}!?Tree {
    return struct {
        fn get(this: This) error{OutOfMemory}!?Tree {
            var i: usize = 0;
            for (try this.tree.children()) |child| {
                switch (child) {
                    .tree => |child_tree| {
                        if (Tree.cast(child_tree)) |correct_tree| {
                            if (i == nth)
                                return correct_tree
                            else
                                i += 1;
                        }
                    },
                    .token => {},
                }
            }
            return null;
        }
    }.get;
}

fn tokenAccessorFn(comptime This: type, comptime tag: syntax.pure.Token.Tag) fn (This) error{OutOfMemory}!?*syntax.Token {
    return struct {
        fn get(this: This) error{OutOfMemory}!?*syntax.Token {
            for (try this.tree.children()) |child| {
                switch (child) {
                    .tree => {},
                    .token => |token| {
                        if (token.tag == tag)
                            return token;
                    },
                }
            }
            return null;
        }
    }.get;
}

pub fn TreeIterator(comptime T: type) type {
    return struct {
        nodes: []syntax.Node,

        pub fn next(this: *@This()) ?T {
            for (this.nodes, 0..) |node, i| {
                switch (node) {
                    .tree => |tree| {
                        if (T.cast(tree)) |correct_tree| {
                            this.nodes = this.nodes[i + 1 ..];
                            return correct_tree;
                        }
                    },
                    .token => {},
                }
            }
            return null;
        }
    };
}

pub const File = struct {
    tree: *syntax.Tree,

    pub usingnamespace AstTreeWithChildren(@This(), .file, Decl);
};

pub const Decl = union(enum) {
    function: Decl.Fn,
    structure: Decl.Struct,
    constant: Decl.Const,

    pub usingnamespace AstUnion(@This());
    pub fn ident(decl: Decl) error{OutOfMemory}!?*syntax.Token {
        return switch (decl) {
            inline else => |variant| variant.ident(),
        };
    }

    pub const Fn = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .decl_fn);
        pub const fnToken = tokenAccessorFn(@This(), .kw_fn);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const params = nthTreeAccessorFn(@This(), Params, 0);
        pub const returns = nthTreeAccessorFn(@This(), Returns, 0);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);

        pub const Params = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTreeWithChildren(@This(), .fn_params, Param);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
        };

        pub const Returns = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTreeWithChildren(@This(), .fn_returns, Return);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
        };

        pub const Param = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTree(@This(), .fn_param);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };

        pub const Return = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTree(@This(), .fn_return);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };
    };

    pub const Struct = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTreeWithChildren(@This(), .decl_struct, Field);
        pub const structToken = tokenAccessorFn(@This(), .kw_struct);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);

        pub const Field = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTree(@This(), .struct_field);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const semi = tokenAccessorFn(@This(), .semi);
        };
    };

    pub const Const = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .decl_const);
        pub const constToken = tokenAccessorFn(@This(), .kw_const);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
        pub const equals = tokenAccessorFn(@This(), .eq);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
        pub const semi = tokenAccessorFn(@This(), .semi);
    };
};

pub const Expr = union(enum) {
    unary: Expr.Unary,
    binary: Expr.Binary,
    literal: Expr.Literal,
    paren: Expr.Paren,
    call: Expr.Call,
    ident: Expr.Ident,

    pub usingnamespace AstUnion(@This());
    pub const Unary = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_unary);
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const minus = tokenAccessorFn(@This(), .minus);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Binary = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_binary);
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const minus = tokenAccessorFn(@This(), .minus);
        pub const star = tokenAccessorFn(@This(), .star);
        pub const slash = tokenAccessorFn(@This(), .slash);
        pub const percent = tokenAccessorFn(@This(), .percent);
        pub const lt2 = tokenAccessorFn(@This(), .lt2);
        pub const gt2 = tokenAccessorFn(@This(), .gt2);
        pub const ampersand = tokenAccessorFn(@This(), .ampersand);
        pub const pipe = tokenAccessorFn(@This(), .pipe);
        pub const caret = tokenAccessorFn(@This(), .caret);
        pub const eq2 = tokenAccessorFn(@This(), .eq);
        pub const bangEq = tokenAccessorFn(@This(), .bang_eq);
        pub const lt = tokenAccessorFn(@This(), .lt);
        pub const gt = tokenAccessorFn(@This(), .gt);
        pub const ltEq = tokenAccessorFn(@This(), .lt_eq);
        pub const gtEq = tokenAccessorFn(@This(), .gt_eq);
        pub const lhs = nthTreeAccessorFn(@This(), Expr, 0);
        pub const rhs = nthTreeAccessorFn(@This(), Expr, 1);
    };

    pub const Literal = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_literal);
        pub const string = tokenAccessorFn(@This(), .string);
        pub const number = tokenAccessorFn(@This(), .number);
    };

    pub const Paren = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_paren);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Call = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_call);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
        pub const args = nthTreeAccessorFn(@This(), Args, 0);

        pub const Args = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTreeWithChildren(@This(), .call_args, Arg);
        };

        pub const Arg = struct {
            tree: *syntax.Tree,

            pub usingnamespace AstTree(@This(), .call_arg);
            pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };
    };

    pub const Ident = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .expr_ident);
        pub const ident = tokenAccessorFn(@This(), .ident);
    };
};

pub const Stmt = union(enum) {
    expr: Stmt.Expr,
    block: Stmt.Block,
    @"return": Stmt.Return,
    @"if": Stmt.If,
    loop: Stmt.Loop,
    @"while": Stmt.While,

    pub usingnamespace AstUnion(@This());
    pub const Expr = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .stmt_expr);
        pub const expr = nthTreeAccessorFn(@This(), ast.Expr, 0);
    };

    pub const Block = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .stmt_block);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const stmt = nthTreeAccessorFn(@This(), Stmt, 0);
    };

    pub const Return = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTreeWithChildren(@This(), .stmt_return, ast.Expr);
        pub const returnToken = tokenAccessorFn(@This(), .kw_return);
    };

    pub const If = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .stmt_if);
        pub const ifToken = tokenAccessorFn(@This(), .kw_if);
        pub const cond = nthTreeAccessorFn(@This(), ast.Expr, 0);
        pub const thenBody = nthTreeAccessorFn(@This(), Stmt.Block, 0);
        pub const elseToken = tokenAccessorFn(@This(), .kw_else);
        pub const elseBody = nthTreeAccessorFn(@This(), Stmt.Block, 1);
    };

    pub const Loop = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .stmt_loop);
        pub const loopToken = tokenAccessorFn(@This(), .kw_loop);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);
    };

    pub const While = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .stmt_while);
        pub const whileToken = tokenAccessorFn(@This(), .kw_while);
        pub const cond = nthTreeAccessorFn(@This(), ast.Expr, 0);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);
    };
};

pub const TypeExpr = union(enum) {
    unary: TypeExpr.Unary,
    ident: TypeExpr.Ident,

    pub usingnamespace AstUnion(@This());
    pub const Unary = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .type_expr_unary);
        pub const star = tokenAccessorFn(@This(), .star);
        pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
    };

    pub const Ident = struct {
        tree: *syntax.Tree,

        pub usingnamespace AstTree(@This(), .type_expr_ident);
        pub const ident = tokenAccessorFn(@This(), .ident);
    };
};
