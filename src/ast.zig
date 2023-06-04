const syntax = @import("syntax.zig");

const ast = @This();

fn unionCastFn(comptime This: type) fn (syntax.Root, syntax.Tree) ?This {
    return struct {
        pub fn cast(root: syntax.Root, tree: syntax.Tree) ?This {
            const tag = root.treeTag(tree);
            inline for (@typeInfo(This).Union.fields) |field|
                if (tag == field.type.tag)
                    return @unionInit(This, field.name, field.type{ .tree = tree });
            return null;
        }
    }.cast;
}

fn treeCastFn(comptime This: type) fn (syntax.Root, syntax.Tree) ?This {
    return struct {
        fn cast(root: syntax.Root, tree: syntax.Tree) ?This {
            if (root.treeTag(tree) != This.tag) return null;
            return This{ .tree = tree };
        }
    }.cast;
}

fn nthTreeAccessorFn(comptime This: type, comptime Tree: type, comptime nth: usize) fn (This, syntax.Root) ?Tree {
    return struct {
        fn get(this: This, root: syntax.Root) ?Tree {
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

fn tokenAccessorFn(comptime This: type, comptime tag: syntax.TokenTag) fn (This, syntax.Root) ?syntax.Token {
    return struct {
        fn get(this: This, root: syntax.Root) ?syntax.Token {
            for (root.treeChildren(this.tree), root.treeChildrenTags(this.tree)) |child, child_tag|
                if (child_tag.asTokenTag() == tag)
                    return child.asToken().?;
            return null;
        }
    }.get;
}

pub const File = struct {
    tree: syntax.Tree,

    pub const tag = syntax.TreeTag.file;
    pub const cast = treeCastFn(@This());
    pub const function = nthTreeAccessorFn(@This(), Decl.Fn, 0);
};

pub const Decl = union(enum) {
    function: Decl.Fn,
    constant: Decl.Const,

    pub const cast = unionCastFn(@This());

    pub const Fn = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.decl_fn;
        pub const cast = treeCastFn(@This());
        pub const fnToken = tokenAccessorFn(@This(), .kw_fn);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const body = nthTreeAccessorFn(@This(), Stmt.Block, 0);
    };

    pub const Const = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.decl_const;
        pub const cast = treeCastFn(@This());
        pub const constToken = tokenAccessorFn(@This(), .kw_const);
        pub const ident = tokenAccessorFn(@This(), .ident);
        pub const eq = tokenAccessorFn(@This(), .eq);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };
};

pub const Expr = union(enum) {
    unary: Expr.Unary,
    binary: Expr.Binary,
    literal: Expr.Literal,
    paren: Expr.Paren,

    pub const cast = unionCastFn(@This());

    pub const Unary = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.expr_unary;
        pub const cast = treeCastFn(@This());
        pub const returnToken = tokenAccessorFn(@This(), .kw_return);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };

    pub const Binary = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.expr_binary;
        pub const cast = treeCastFn(@This());
        pub const plus = tokenAccessorFn(@This(), .plus);
        pub const star = tokenAccessorFn(@This(), .star);
        pub const lhs = nthTreeAccessorFn(@This(), Expr, 0);
        pub const rhs = nthTreeAccessorFn(@This(), Expr, 1);
    };

    pub const Literal = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.expr_literal;
        pub const cast = treeCastFn(@This());
        pub const string = tokenAccessorFn(@This(), .string);
        pub const number = tokenAccessorFn(@This(), .number);
    };

    pub const Paren = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.expr_paren;
        pub const cast = treeCastFn(@This());
        pub const lParen = tokenAccessorFn(@This(), .l_paren);
        pub const rParen = tokenAccessorFn(@This(), .r_paren);
        pub const expr = nthTreeAccessorFn(@This(), Expr, 0);
    };
};

pub const Stmt = union(enum) {
    expr: Stmt.Expr,
    block: Stmt.Block,

    pub const cast = unionCastFn(@This());

    pub const Expr = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.stmt_expr;
        pub const cast = treeCastFn(@This());
        pub const expr = nthTreeAccessorFn(@This(), ast.Expr, 0);
    };

    pub const Block = struct {
        tree: syntax.Tree,

        pub const tag = syntax.TreeTag.stmt_block;
        pub const cast = treeCastFn(@This());
        pub const lBrace = tokenAccessorFn(@This(), .l_brace);
        pub const rBrace = tokenAccessorFn(@This(), .r_brace);
        pub const stmt = nthTreeAccessorFn(@This(), Stmt, 0);
    };
};
