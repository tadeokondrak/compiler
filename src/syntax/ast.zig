const std = @import("std");
const syntax = @import("../syntax.zig");

const ast = @This();

fn unionCastFn(comptime This: type) fn (syntax.pure.Root, syntax.pure.Tree.Index) ?This {
    return struct {
        pub fn cast(root: syntax.pure.Root, tree: syntax.pure.Tree.Index) ?This {
            inline for (@typeInfo(This).Union.fields) |field|
                if (field.type.cast(root, tree)) |correct_tree|
                    return @unionInit(This, field.name, correct_tree);
            return null;
        }
    }.cast;
}

fn treeCastFn(comptime This: type, comptime tag: syntax.pure.Tree.Tag) fn (syntax.pure.Root, syntax.pure.Tree.Index) ?This {
    return struct {
        fn cast(root: syntax.pure.Root, tree: syntax.pure.Tree.Index) ?This {
            if (root.treeTag(tree) != tag) return null;
            return This{ .tree = tree };
        }
    }.cast;
}

fn treeIteratorFn(comptime This: type, comptime Tree: type) fn (This, syntax.pure.Root) ast.TreeIterator(Tree) {
    return struct {
        fn iter(this: This, root: syntax.pure.Root) ast.TreeIterator(Tree) {
            return ast.TreeIterator(Tree){
                .nodes = root.treeChildren(this.tree),
            };
        }
    }.iter;
}

fn treeFormatFn(comptime This: type, comptime tag: syntax.pure.Tree.Tag) fn (This, comptime []const u8, std.fmt.FormatOptions, anytype) anyerror!void {
    return struct {
        fn format(this: This, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(@tagName(tag) ++ "(");
            try writer.print("{}", .{@enumToInt(this.tree)});
            try writer.writeAll(")");
        }
    }.format;
}

fn nthTreeAccessorFn(comptime This: type, comptime Tree: type, comptime nth: usize) fn (This, syntax.pure.Root) ?Tree {
    return struct {
        fn get(this: This, root: syntax.pure.Root) ?Tree {
            var i: usize = 0;
            for (root.treeChildren(this.tree)) |child| {
                if (child.asTree()) |child_tree| {
                    if (Tree.cast(root, child_tree)) |correct_tree| {
                        if (i == nth)
                            return correct_tree
                        else
                            i += 1;
                    }
                }
            }
            return null;
        }
    }.get;
}

fn tokenAccessorFn(comptime This: type, comptime tag: syntax.pure.Token.Tag) fn (This, syntax.pure.Root) ?syntax.pure.Token.Index {
    return struct {
        fn get(this: This, root: syntax.pure.Root) ?syntax.pure.Token.Index {
            for (root.treeChildren(this.tree), root.treeChildrenTags(this.tree)) |child, child_tag|
                if (child_tag.asTokenTag() == tag)
                    return child.asToken().?;
            return null;
        }
    }.get;
}

pub fn TreeIterator(comptime T: type) type {
    return struct {
        nodes: []const syntax.pure.Node.Index,

        pub fn next(this: *@This(), root: syntax.pure.Root) ?T {
            for (this.nodes, 0..) |node, i| {
                if (node.asTree()) |tree| {
                    if (T.cast(root, tree)) |correct_tree| {
                        this.nodes = this.nodes[i + 1 ..];
                        return correct_tree;
                    }
                }
            }
            return null;
        }
    };
}

pub const File = struct {
    tree: syntax.pure.Tree.Index,

    pub const cast = treeCastFn(@This(), .file);
    pub const format = treeFormatFn(@This(), .file);
    pub const decls = treeIteratorFn(@This(), Decl);
};

pub const Decl = union(enum) {
    function: Decl.Fn,
    structure: Decl.Struct,
    constant: Decl.Const,

    pub const cast = unionCastFn(@This());

    pub const Fn = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .decl_fn);
        pub const format = treeFormatFn(@This(), .decl_fn);
        pub const fnToken = tokenAccessorFn(@This(), .kw_fn);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const params = nthTreeAccessorFn(@This(), Params, 0);
        pub const returns = nthTreeAccessorFn(@This(), Returns, 0);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);

        pub const Params = struct {
            tree: syntax.pure.Tree.Index,

            pub const cast = treeCastFn(@This(), .fn_params);
            pub const format = treeFormatFn(@This(), .fn_params);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
            pub const params = treeIteratorFn(@This(), Param);
        };

        pub const Returns = struct {
            tree: syntax.pure.Tree.Index,

            pub const cast = treeCastFn(@This(), .fn_returns);
            pub const format = treeFormatFn(@This(), .fn_returns);
            pub const lParen = tokenAccessorFn(@This(), .l_paren);
            pub const rParen = tokenAccessorFn(@This(), .r_paren);
            pub const returns = treeIteratorFn(@This(), Return);
        };

        pub const Param = struct {
            tree: syntax.pure.Tree.Index,

            pub const cast = treeCastFn(@This(), .fn_param);
            pub const format = treeFormatFn(@This(), .fn_param);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };

        pub const Return = struct {
            tree: syntax.pure.Tree.Index,

            pub const cast = treeCastFn(@This(), .fn_return);
            pub const format = treeFormatFn(@This(), .fn_return);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const comma = tokenAccessorFn(@This(), .comma);
        };
    };

    pub const Struct = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .decl_struct);
        pub const format = treeFormatFn(@This(), .decl_struct);
        pub const structToken = tokenAccessorFn(@This(), .kw_struct);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const fields = treeIteratorFn(@This(), Field);

        pub const Field = struct {
            tree: syntax.pure.Tree.Index,

            pub const cast = treeCastFn(@This(), .struct_field);
            pub const format = treeFormatFn(@This(), .struct_field);
            pub const ident = tokenAccessorFn(@This(), .ident);
            pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
            pub const semi = tokenAccessorFn(@This(), .semi);
        };
    };

    pub const Const = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .decl_const);
        pub const format = treeFormatFn(@This(), .decl_const);
        pub const constToken = tokenAccessorFn(@This(), .kw_const);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const typeExpr = nthTreeAccessorFn(@This(), TypeExpr, 0);
        pub const equals = tokenAccessorFn(@This(), .equals);
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

    pub const Unary = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_unary);
        pub const format = treeFormatFn(@This(), .expr_unary);
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const minus = tokenAccessorFn(@This(), .minus);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Binary = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_binary);
        pub const format = treeFormatFn(@This(), .expr_binary);
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const minus = tokenAccessorFn(@This(), .minus);
        pub const star = tokenAccessorFn(@This(), .star);
        pub const slash = tokenAccessorFn(@This(), .slash);
        pub const percent = tokenAccessorFn(@This(), .percent);
        pub const lhs = nthTreeAccessorFn(@This(), Expr, 0);
        pub const rhs = nthTreeAccessorFn(@This(), Expr, 1);
    };

    pub const Literal = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_literal);
        pub const format = treeFormatFn(@This(), .expr_literal);
        pub const string = tokenAccessorFn(@This(), .string);
        pub const number = tokenAccessorFn(@This(), .number);
    };

    pub const Paren = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_paren);
        pub const format = treeFormatFn(@This(), .expr_paren);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Call = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_call);
        pub const format = treeFormatFn(@This(), .expr_call);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Ident = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .expr_ident);
        pub const format = treeFormatFn(@This(), .expr_ident);
        pub const ident = tokenAccessorFn(@This(), .ident);
    };
};

pub const Stmt = union(enum) {
    expr: Stmt.Expr,
    block: Stmt.Block,
    @"return": Stmt.Return,

    pub const cast = unionCastFn(@This());

    pub const Expr = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .stmt_expr);
        pub const format = treeFormatFn(@This(), .stmt_expr);
        pub const expr = nthTreeAccessorFn(@This(), ast.Expr, 0);
    };

    pub const Block = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .stmt_block);
        pub const format = treeFormatFn(@This(), .stmt_block);
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const stmt = nthTreeAccessorFn(@This(), Stmt, 0);
    };

    pub const Return = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .stmt_return);
        pub const format = treeFormatFn(@This(), .stmt_return);
        pub const returnToken = tokenAccessorFn(@This(), .kw_return);
        pub const expr = nthTreeAccessorFn(@This(), ast.Expr, 0);
    };
};

pub const TypeExpr = union(enum) {
    ident: TypeExpr.Ident,

    pub const cast = unionCastFn(@This());

    pub const Ident = struct {
        tree: syntax.pure.Tree.Index,

        pub const cast = treeCastFn(@This(), .type_expr_ident);
        pub const format = treeFormatFn(@This(), .type_expr_ident);
        pub const ident = tokenAccessorFn(@This(), .ident);
    };
};
