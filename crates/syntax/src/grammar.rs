use super::{parser::MarkClosed, parser::Parser, ExprPrec, Syntax, TypePrec};

pub(super) fn parse_file(p: &mut Parser) {
    let m = p.begin();
    while !p.at(Syntax::Eof) {
        parse_item(p);
    }
    p.end(m, Syntax::File);
}

fn parse_stmt(p: &mut Parser) {
    assert!(p.at_any(EXPR_START) || p.at_any(ITEM_START));
    let m = p.begin();
    match p.current() {
        t!("identifier") if p.at_keyword(t!("let")) => {
            let m = p.begin();
            p.bump(t!("let"));
            p.expect(t!("identifier"));
            p.expect(t!("="));
            parse_expr(p);
            p.end(m, Syntax::LetStmt);
        }
        _ if p.at_any(EXPR_START) => parse_expr(p),
        _ if p.at_any(ITEM_START) => parse_item(p),
        _ => unreachable!(),
    }
    if !p.eat(t!(";")) && !p.at(t!("}")) && !p.at(Syntax::Eof) {
        if p.at_newline() {
            // make sure the newline is in the node
            p.bump_newline();
        } else {
            p.error(&format!("expected semicolon, not {:?}", p.current()));
        }
    }
    p.end(m, Syntax::ExprStmt);
}

const EXPR_START: &[Syntax] = &[
    t!("{"),
    t!("("),
    t!("number"),
    t!("character"),
    t!("string"),
    t!("identifier"),
];

const ITEM_START: &[Syntax] = &[t!("identifier")];
const TYPE_START: &[Syntax] = &[t!("identifier"), t!("(")];

fn parse_item(p: &mut Parser) {
    assert!(p.at_any(ITEM_START));
    match p.current() {
        t!("identifier") if p.at_keyword(t!("fn")) => {
            let m = p.begin();
            p.bump(t!("fn"));
            p.expect(t!("identifier"));
            p.expect(t!("("));
            while !p.at(t!(")")) && !p.at(Syntax::Eof) {
                parse_parameter(p);
            }
            p.expect(t!(")"));
            // TODO allow newline here
            if !p.at(t!("{")) && !p.at(t!(";")) && !p.at(Syntax::Eof) {
                parse_type(p);
            }
            match p.current() {
                t!("{") => {
                    parse_block_expr(p);
                }
                t!(";") => {
                    p.bump(t!(";"));
                }
                _ => p.error("expected { or ;"),
            }
            p.end(m, Syntax::FnItem);
        }
        t!("identifier") if p.at_keyword(t!("struct")) => {
            let m = p.begin();
            p.bump(t!("struct"));
            p.expect(t!("identifier"));
            p.expect(t!("{"));
            while !p.at(t!("}")) && !p.at(Syntax::Eof) {
                let member = p.begin();
                p.expect(t!("identifier"));
                parse_type(p);
                p.expect(t!(";")); // TODO allow newline
                p.end(member, Syntax::Member);
            }
            p.expect(t!("}"));
            p.end(m, Syntax::StructItem);
        }
        t!("identifier") if p.at_keyword(t!("const")) => {
            let m = p.begin();
            p.bump(t!("const"));
            p.expect(t!("identifier"));
            p.expect(t!(":"));
            parse_type(p);
            p.expect(t!("="));
            parse_expr(p);
            p.expect(t!(";"));
            p.end(m, Syntax::StructItem);
        }
        _ => unreachable!("{:?}", p.nth_keyword(0)),
    }
}

fn parse_parameter(p: &mut Parser) {
    let m = p.begin();
    p.expect(t!("identifier"));
    parse_type(p);
    if !p.at(t!(")")) && !p.eat(t!(",")) {
        if p.at_newline() {
            // make sure the newline is in the node
            p.bump_newline();
        } else {
            p.error(&format!("expected comma, not {:?}", p.current()));
        }
    }
    p.end(m, Syntax::Parameter);
}

fn parse_expr(p: &mut Parser) {
    parse_expr_precedence(p, ExprPrec::Zero as i8);
}

fn parse_expr_precedence(p: &mut Parser, min_prec: i8) -> MarkClosed {
    let mut lhs = {
        let op = p.current_operator();
        if let Some(op_prec) = op.expr_prefix_prec() {
            let r_prec = op_prec as i8;
            let m = p.begin();
            p.bump(op);
            parse_expr_precedence(p, r_prec);
            p.end(m, Syntax::UnaryExpr)
        } else {
            parse_expr_delimited(p)
        }
    };
    loop {
        let op = p.current_operator();
        if let Some(op_prec) = op.expr_postfix_prec() {
            let l_prec = op_prec as i8;
            if l_prec < min_prec {
                break;
            }
            let m = p.begin_at(lhs);
            p.bump(op);
            lhs = match op {
                t!("(") => {
                    while !p.at(t!(")")) && !p.at(Syntax::Eof) {
                        parse_argument(p);
                    }
                    p.expect(t!(")"));
                    p.end(m, Syntax::CallExpr)
                }
                t!("[") => {
                    parse_expr(p);
                    p.expect(t!("]"));
                    p.end(m, Syntax::IndexExpr)
                }
                t!(".") => {
                    p.expect_keyword(t!("identifier"));
                    p.end(m, Syntax::FieldExpr)
                }
                _ => p.end(m, Syntax::UnaryExpr),
            };
            continue;
        }
        if let Some((op_prec, op_assoc)) = op.expr_infix_prec_assoc() {
            let l_prec = op_prec as i8 - op_assoc as i8;
            let r_prec = op_prec as i8 + op_assoc as i8;
            if l_prec < min_prec {
                break;
            }
            let m = p.begin_at(lhs);
            p.bump(op);
            parse_expr_precedence(p, r_prec);
            lhs = p.end(m, Syntax::BinaryExpr);
            continue;
        }
        break;
    }
    lhs
}

fn parse_argument(p: &mut Parser) {
    let m = p.begin();
    parse_expr(p);
    if !p.at(t!(")")) && !p.eat(t!(",")) {
        if p.at_newline() {
            // make sure the newline is in the node
            p.bump_newline();
        } else {
            p.error(&format!("expected comma, not {:?}", p.current()));
        }
    }
    p.end(m, Syntax::Argument);
}

fn parse_expr_delimited(p: &mut Parser) -> MarkClosed {
    assert!(p.at_any(EXPR_START), "{:?}", p.current());
    let kind = p.current();
    match kind {
        t!("(") => {
            let m = p.begin();
            p.bump(kind);
            parse_expr(p);
            p.expect(t!(")"));
            p.end(m, Syntax::ParenExpr)
        }
        t!("identifier") if p.at_keyword(t!("identifier")) => {
            let m = p.begin();
            p.bump(kind);
            p.end(m, Syntax::NameExpr)
        }
        t!("number") | t!("character") | t!("string") => {
            let m = p.begin();
            p.bump(kind);
            p.end(m, Syntax::LiteralExpr)
        }
        t!("identifier") if p.at_keyword(t!("if")) => {
            let m = p.begin();
            p.bump(t!("if"));
            parse_expr(p);
            parse_block_expr(p);
            if p.eat_keyword(t!("else")) {
                parse_block_expr(p);
            }
            p.end(m, Syntax::IfExpr)
        }
        t!("identifier") if p.at_keyword(t!("loop")) => {
            let m = p.begin();
            p.bump(t!("loop"));
            parse_block_expr(p);
            p.end(m, Syntax::LoopExpr)
        }
        t!("identifier") if p.at_keyword(t!("while")) => {
            let m = p.begin();
            p.bump(t!("while"));
            parse_expr(p);
            parse_block_expr(p);
            p.end(m, Syntax::WhileExpr)
        }
        t!("{") => parse_block_expr(p),
        t!("identifier") if p.at_keyword(t!("break")) => {
            let m = p.begin();
            p.bump(t!("break"));
            if p.at_any(EXPR_START) && !p.at_newline() {
                parse_expr(p);
            }
            p.end(m, Syntax::BreakExpr)
        }
        t!("identifier") if p.at_keyword(t!("return")) => {
            let m = p.begin();
            p.bump(t!("return"));
            if p.at_any(EXPR_START) && !p.at_newline() {
                parse_expr(p);
            }
            p.end(m, Syntax::ReturnExpr)
        }
        t!("identifier") if p.at_keyword(t!("continue")) => {
            let m = p.begin();
            p.bump(t!("continue"));
            if p.at_any(EXPR_START) && !p.at_newline() {
                parse_expr(p);
            }
            p.end(m, Syntax::ContinueExpr)
        }
        _ => unreachable!(),
    }
}

fn parse_block_expr(p: &mut Parser) -> MarkClosed {
    let m = p.begin();
    p.bump(t!("{"));
    while !p.at(t!("}")) && !p.at(Syntax::Eof) {
        if !p.at_any(EXPR_START) && !p.at_any(ITEM_START) {
            let m = p.begin();
            p.error(&format!("expected statement, got {:?}", p.current()));
            while !p.at_any(EXPR_START)
                && !p.at_any(ITEM_START)
                && !p.at(t!("}"))
                && !p.at(Syntax::Eof)
            {
                p.bump_any();
            }
            p.end(m, Syntax::Error);
        } else {
            parse_stmt(p);
        }

        if p.at(t!("}")) || p.at(Syntax::Eof) {
            break;
        }
    }
    p.expect(t!("}"));
    p.end(m, Syntax::BlockExpr)
}

fn parse_type(p: &mut Parser) {
    parse_type_precedence(p, TypePrec::Zero as i8);
}

fn parse_type_precedence(p: &mut Parser, _min_prec: i8) -> MarkClosed {
    let lhs = {
        let op = p.current_operator();
        if let Some(op_prec) = op.type_prefix_prec() {
            let r_prec = op_prec as i8;
            let m = p.begin();
            p.bump(op);
            parse_type_precedence(p, r_prec);
            match op {
                t!("ptr") => p.end(m, Syntax::PointerType),
                t!("slice") => p.end(m, Syntax::SliceType),
                _ => unreachable!(),
            }
        } else {
            parse_type_delimited(p)
        }
    };
    lhs
}

fn parse_type_delimited(p: &mut Parser) -> MarkClosed {
    assert!(p.at_any(TYPE_START), "{:?}", p.current());
    let kind = p.current();
    match kind {
        t!("(") => {
            let m = p.begin();
            p.bump(kind);
            parse_type(p);
            p.expect(t!(")"));
            p.end(m, Syntax::ParenType)
        }
        t!("identifier") if p.at_keyword(t!("identifier")) => {
            let m = p.begin();
            p.bump(kind);
            p.end(m, Syntax::NameType)
        }
        _ => unreachable!(),
    }
}
