const std = @import("std");
const syntax = @import("../syntax.zig");

const ast = @This();

comptime {
    std.testing.refAllDeclsRecursive(ast);
}

fn unionCastFn(comptime This: type) fn (*syntax.Tree) ?This {
    return struct {
        pub fn cast(tree: *syntax.Tree) ?This {
            inline for (@typeInfo(This).Union.fields) |field|
                if (field.type.cast(tree)) |correct_tree|
                    return @unionInit(This, field.name, correct_tree);
            return null;
        }
    }.cast;
}

fn unionTreeFn(comptime This: type) fn (This) *syntax.Tree {
    return struct {
        pub fn tree(this: This) *syntax.Tree {
            return switch (this) {
                inline else => |variant| variant.tree,
            };
        }
    }.tree;
}

fn unionPtrFn(comptime This: type) fn (This) syntax.AstPtr(This) {
    return struct {
        pub fn ptr(this: This) syntax.AstPtr(This) {
            return .{ .span = this.span() };
        }
    }.ptr;
}

fn unionSpanFn(comptime This: type) fn (This) syntax.pure.Span {
    return struct {
        pub fn span(this: This) syntax.pure.Span {
            return switch (this) {
                inline else => |variant| variant.span(),
            };
        }
    }.span;
}

fn treePtrFn(comptime This: type) fn (This) syntax.AstPtr(This) {
    return struct {
        pub fn ptr(this: This) syntax.AstPtr(This) {
            return .{ .span = this.tree.span() };
        }
    }.ptr;
}

fn treeSpanFn(comptime This: type) fn (This) syntax.pure.Span {
    return struct {
        pub fn ptr(this: This) syntax.pure.Span {
            return this.tree.span();
        }
    }.ptr;
}

fn treeCastFn(comptime This: type, comptime tag: syntax.pure.Tree.Tag) fn (*syntax.Tree) ?This {
    return struct {
        fn cast(tree: *syntax.Tree) ?This {
            if (tree.tag != tag) return null;
            return This{ .tree = tree };
        }
    }.cast;
}

fn treeIteratorFn(comptime This: type, comptime Tree: type) fn (This) error{OutOfMemory}!ast.TreeIterator(Tree) {
    return struct {
        fn iter(this: This) error{OutOfMemory}!ast.TreeIterator(Tree) {
            return .{ .nodes = try this.tree.children() };
        }
    }.iter;
}

fn treeFormatFn(comptime This: type, comptime tag: syntax.pure.Tree.Tag) fn (This, comptime []const u8, std.fmt.FormatOptions, anytype) anyerror!void {
    return struct {
        fn format(this: This, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(@tagName(tag) ++ "(");
            try writer.print("{}", .{@intFromEnum(this.tree)});
            try writer.writeAll(")");
        }
    }.format;
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

    pub const cast = treeCastFn(@This(), .file);
    pub const ptr = treePtrFn(@This());
    pub const span = treeSpanFn(@This());
    pub const format = treeFormatFn(@This(), .file);
    pub const decls = treeIteratorFn(@This(), Decl);
};

pub const Decl = union(enum) {
    function: Decl.Fn,
    structure: Decl.Struct,
    constant: Decl.Const,

    pub const cast = unionCastFn(@This());
    pub const tree = unionTreeFn(@This());
    pub const ptr = unionPtrFn(@This());
    pub const span = unionSpanFn(@This());

    pub fn ident(decl: Decl) error{OutOfMemory}!?*syntax.Token {
        return switch (decl) {
            inline else => |variant| variant.ident(),
        };
    }

    pub const Fn = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .decl_fn);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .decl_fn);
        pub const fnToken = tokenAccessorFn(@This(), .kw_fn);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const params = nthTreeAccessorFn(@This(), Params, 0);
        pub const returns = nthTreeAccessorFn(@This(), Returns, 0);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);

        pub const Params = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .fn_params);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .fn_params);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
            pub const params = treeIteratorFn(@This(), Param);
        };

        pub const Returns = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .fn_returns);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .fn_returns);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
            pub const returns = treeIteratorFn(@This(), Return);
        };

        pub const Param = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .fn_param);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .fn_param);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };

        pub const Return = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .fn_return);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .fn_return);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };
    };

    pub const Struct = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .decl_struct);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .decl_struct);
        pub const structToken = tokenAccessorFn(@This(), .kw_struct);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const fields = treeIteratorFn(@This(), Field);

        pub const Field = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .struct_field);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .struct_field);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const semi = tokenAccessorFn(@This(), .semi);
        };
    };

    pub const Const = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .decl_const);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .decl_const);
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

    pub const cast = unionCastFn(@This());
    pub const tree = unionTreeFn(@This());
    pub const ptr = unionPtrFn(@This());
    pub const span = unionSpanFn(@This());

    pub const Unary = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .expr_unary);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_unary);
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const minus = tokenAccessorFn(@This(), .minus);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Binary = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .expr_binary);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_binary);
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

        pub const cast = treeCastFn(@This(), .expr_literal);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_literal);
        pub const string = tokenAccessorFn(@This(), .string);
        pub const number = tokenAccessorFn(@This(), .number);
    };

    pub const Paren = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .expr_paren);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_paren);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Call = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .expr_call);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_call);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
        pub const args = nthTreeAccessorFn(@This(), Args, 0);

        pub const Args = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .call_args);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .call_args);
            pub const args = treeIteratorFn(@This(), Arg);
        };

        pub const Arg = struct {
            tree: *syntax.Tree,

            pub const cast = treeCastFn(@This(), .call_arg);
            pub const ptr = treePtrFn(@This());
            pub const span = treeSpanFn(@This());
            pub const format = treeFormatFn(@This(), .call_arg);
            pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };
    };

    pub const Ident = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .expr_ident);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .expr_ident);
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

    pub const cast = unionCastFn(@This());
    pub const tree = unionTreeFn(@This());
    pub const ptr = unionPtrFn(@This());
    pub const span = unionSpanFn(@This());

    pub const Expr = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_expr);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_expr);
        pub const expr = nthTreeAccessorFn(@This(), ast.Expr, 0);
    };

    pub const Block = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_block);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_block);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const stmt = nthTreeAccessorFn(@This(), Stmt, 0);
    };

    pub const Return = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_return);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_return);
        pub const returnToken = tokenAccessorFn(@This(), .kw_return);
        pub const exprs = treeIteratorFn(@This(), ast.Expr);
    };

    pub const If = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_if);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_if);
        pub const ifToken = tokenAccessorFn(@This(), .kw_if);
        pub const cond = nthTreeAccessorFn(@This(), ast.Expr, 0);
        pub const thenBody = nthTreeAccessorFn(@This(), Stmt.Block, 0);
        pub const elseToken = tokenAccessorFn(@This(), .kw_else);
        pub const elseBody = nthTreeAccessorFn(@This(), Stmt.Block, 1);
    };

    pub const Loop = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_loop);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_loop);
        pub const loopToken = tokenAccessorFn(@This(), .kw_loop);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);
    };

    pub const While = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .stmt_while);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .stmt_while);
        pub const whileToken = tokenAccessorFn(@This(), .kw_while);
        pub const cond = nthTreeAccessorFn(@This(), ast.Expr, 0);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);
    };
};

pub const TypeExpr = union(enum) {
    unary: TypeExpr.Unary,
    ident: TypeExpr.Ident,

    pub const cast = unionCastFn(@This());
    pub const tree = unionTreeFn(@This());
    pub const ptr = unionPtrFn(@This());
    pub const span = unionSpanFn(@This());

    pub const Unary = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .type_expr_unary);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .type_expr_unary);
        pub const star = tokenAccessorFn(@This(), .star);
        pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
    };

    pub const Ident = struct {
        tree: *syntax.Tree,

        pub const cast = treeCastFn(@This(), .type_expr_ident);
        pub const ptr = treePtrFn(@This());
        pub const span = treeSpanFn(@This());
        pub const format = treeFormatFn(@This(), .type_expr_ident);
        pub const ident = tokenAccessorFn(@This(), .ident);
    };
};
