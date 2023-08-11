use super::{
    lower_type_ref, Analysis, Body, Expr, ExprId, Function, IntSize, ItemId, Items, Name, Signed,
    Stmt, Type,
};
use crate::TypeId;
use std::collections::HashMap;

#[derive(Debug)]
pub struct InferenceResult {
    pub param_tys: Box<[TypeId]>,
    pub return_ty: TypeId,
    pub exprs: HashMap<ExprId, TypeId>,
}

pub fn infer(
    analysis: &mut Analysis,
    items: &Items,
    func: &Function,
    body: &Body,
) -> InferenceResult {
    let mut ctx = InferCtx {
        analysis,
        items,
        func,
        body,
        exprs: HashMap::new(),
    };
    let param_tys = func
        .param_tys
        .iter()
        .map(|&ty| lower_type_ref(&mut ctx.analysis, &ctx.items, &func.type_refs, ty))
        .collect();
    let return_ty = lower_type_ref(
        &mut ctx.analysis,
        &ctx.items,
        &func.type_refs,
        func.return_ty,
    );
    infer_expr(&mut ctx, body.expr);

    InferenceResult {
        return_ty,
        param_tys,
        exprs: ctx.exprs,
    }
}

struct InferCtx<'a> {
    analysis: &'a mut Analysis,
    items: &'a Items,
    func: &'a Function,
    body: &'a Body,
    exprs: HashMap<ExprId, TypeId>,
}

fn infer_expr(ctx: &mut InferCtx, expr: ExprId) -> TypeId {
    let type_id = match &ctx.body.exprs[expr] {
        Expr::Missing => ctx.analysis.intern_type(Type::Error),
        Expr::Unit => ctx.analysis.intern_type(Type::Unit),
        Expr::Name(name) => {
            let item_ty = ctx
                .items
                .items
                .iter()
                .find_map(|item| match item {
                    &ItemId::Function(func) => match &ctx.items.functions[func].name {
                        Name::Present(func_name) if func_name == name => Some(func),
                        _ => None,
                    },
                    ItemId::Record(_) => None,
                    ItemId::Const(_) => None,
                    ItemId::Enum(_) => None,
                })
                .map(|func| {
                    let func = &ctx.items.functions[func];
                    Type::SpecificFn {
                        name: func.name.clone(),
                        ret_ty: lower_type_ref(
                            &mut ctx.analysis,
                            &ctx.items,
                            &func.type_refs,
                            func.return_ty,
                        ),
                        param_tys: func
                            .param_tys
                            .iter()
                            .map(|&ty| {
                                lower_type_ref(&mut ctx.analysis, &ctx.items, &func.type_refs, ty)
                            })
                            .collect(),
                    }
                })
                .map(|ty| ctx.analysis.intern_type(ty));
            let param_ty = ctx
                .body
                .param_names
                .iter()
                .enumerate()
                .find(|&(_, it)| it == name.as_str())
                .map(|(i, _)| {
                    lower_type_ref(
                        &mut ctx.analysis,
                        &ctx.items,
                        &ctx.func.type_refs,
                        ctx.func.param_tys[i],
                    )
                });
            param_ty
                .or(item_ty)
                .unwrap_or_else(|| ctx.analysis.intern_type(Type::Error))
        }
        Expr::Number(_) => ctx
            .analysis
            .intern_type(Type::Int(Signed::No, IntSize::Size32)),
        &Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr(ctx, cond);
            infer_expr(ctx, then_expr);
            else_expr.map(|expr| infer_expr(ctx, expr));
            ctx.analysis.intern_type(Type::Unit)
        }
        &Expr::Loop { body } => {
            infer_expr(ctx, body);
            ctx.analysis.intern_type(Type::Never)
        }
        Expr::Block { body } => {
            for stmt in body.iter() {
                match stmt {
                    Stmt::Let(_, _) => todo!(),
                    &Stmt::Expr(expr) => {
                        infer_expr(ctx, expr);
                    }
                }
            }
            ctx.analysis.intern_type(Type::Unit)
        }
        &Expr::Unary { op: _, operand } => {
            let operand_ty = infer_expr(ctx, operand);
            operand_ty
        }
        &Expr::Binary { op: _, lhs, rhs } => {
            let lhs_ty = infer_expr(ctx, lhs);
            let _rhs_ty = infer_expr(ctx, rhs);
            lhs_ty
        }
        Expr::Break => ctx.analysis.intern_type(Type::Never),
        Expr::Continue => ctx.analysis.intern_type(Type::Never),
        &Expr::Return { value } => {
            infer_expr(ctx, value);
            ctx.analysis.intern_type(Type::Never)
        }
        Expr::Call { callee, args } => {
            let callee_ty = infer_expr(ctx, *callee);
            let &Type::SpecificFn { ret_ty, .. } = &ctx.analysis.types[callee_ty] else {
                eprintln!("called non-function type");
                return ctx.analysis.intern_type(Type::Error);
            };
            for &arg in args.iter() {
                infer_expr(ctx, arg);
            }
            ret_ty
        }
        &Expr::Index { base, index: _ } => {
            infer_expr(ctx, base);
            eprintln!("Expr::Index unimplemented");
            ctx.analysis.intern_type(Type::Error)
        }
        Expr::Field { base, name } => {
            let base_ty = infer_expr(ctx, *base);
            match ctx.analysis.types[base_ty] {
                Type::Ptr(ptr_ty) => match ctx.analysis.types[ptr_ty] {
                    Type::Record(record_id) => {
                        let record = &ctx.items.records[record_id];
                        let field = record
                            .fields
                            .iter()
                            .find(|field| field.name == *name.as_str())
                            .unwrap();
                        lower_type_ref(&mut ctx.analysis, &ctx.items, &record.type_refs, field.ty)
                    }
                    _ => todo!(),
                },
                Type::Record(record_id) => {
                    let record = &ctx.items.records[record_id];
                    let field = record
                        .fields
                        .iter()
                        .find(|field| field.name == *name.as_str())
                        .unwrap();
                    lower_type_ref(&mut ctx.analysis, &ctx.items, &record.type_refs, field.ty)
                }
                _ => todo!(),
            }
        }
    };
    ctx.exprs.insert(expr, type_id);
    type_id
}
