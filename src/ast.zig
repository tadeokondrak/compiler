const syntax = @import("syntax.zig");
pub const File = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .file, @This());
    }
    pub fn function(this: @This(), root: syntax.Root) ?DeclFn {
        return syntax.findNthTree(root, this.tree, DeclFn, 0);
    }
};
pub const DeclFn = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .decl_fn, @This());
    }
    pub fn kw_fn(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .kw_fn);
    }
    pub fn ident(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .ident);
    }
    pub fn l_paren(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .l_paren);
    }
    pub fn r_paren(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .r_paren);
    }
    pub fn body(this: @This(), root: syntax.Root) ?StmtBlock {
        return syntax.findNthTree(root, this.tree, StmtBlock, 0);
    }
};
pub const Decl = union(enum) {
    function: DeclFn,
    constant: DeclConst,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return switch (root.treeTag(tree)) {
            .decl_fn => .{ .function = .{ .tree = tree } },
            .decl_const => .{ .constant = .{ .tree = tree } },
            else => null,
        };
    }
};
pub const DeclConst = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .decl_const, @This());
    }
    pub fn kw_const(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .kw_const);
    }
    pub fn ident(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .ident);
    }
    pub fn eq(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .eq);
    }
    pub fn expr(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 0);
    }
};
pub const StmtBlock = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .stmt_block, @This());
    }
    pub fn l_brace(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .l_brace);
    }
    pub fn stmts(this: @This(), root: syntax.Root) ?Stmt {
        return syntax.findNthTree(root, this.tree, Stmt, 0);
    }
    pub fn r_brace(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .r_brace);
    }
};
pub const Expr = union(enum) {
    unary: ExprUnary,
    binary: ExprBinary,
    literal: ExprLiteral,
    paren: ExprParen,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return switch (root.treeTag(tree)) {
            .expr_unary => .{ .unary = .{ .tree = tree } },
            .expr_binary => .{ .binary = .{ .tree = tree } },
            .expr_literal => .{ .literal = .{ .tree = tree } },
            .expr_paren => .{ .paren = .{ .tree = tree } },
            else => null,
        };
    }
};
pub const Stmt = union(enum) {
    expr: StmtExpr,
    block: StmtBlock,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return switch (root.treeTag(tree)) {
            .stmt_expr => .{ .expr = .{ .tree = tree } },
            .stmt_block => .{ .block = .{ .tree = tree } },
            else => null,
        };
    }
};
pub const StmtExpr = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .stmt_expr, @This());
    }
    pub fn expr(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 0);
    }
};
pub const ExprUnary = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .expr_unary, @This());
    }
    pub fn kw_return(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .kw_return);
    }
    pub fn expr(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 0);
    }
};
pub const ExprBinary = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .expr_binary, @This());
    }
    pub fn lhs(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 0);
    }
    pub fn plus(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .plus);
    }
    pub fn star(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .star);
    }
    pub fn rhs(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 1);
    }
};
pub const ExprLiteral = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .expr_literal, @This());
    }
    pub fn string(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .string);
    }
    pub fn number(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .number);
    }
};
pub const ExprParen = struct {
    tree: syntax.Tree,
    pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {
        return syntax.castTree(root, tree, .expr_paren, @This());
    }
    pub fn l_paren(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .l_paren);
    }
    pub fn expr(this: @This(), root: syntax.Root) ?Expr {
        return syntax.findNthTree(root, this.tree, Expr, 0);
    }
    pub fn r_paren(this: @This(), root: syntax.Root) ?syntax.Token {
        return syntax.findToken(root, this.tree, .r_paren);
    }
};
