use super::{
    lower_type_ref, Analysis, Body, Expr, ExprId, Function, ItemId, Items, Name, Stmt, Type,
};
use crate::{TypeId, TypeVarId};
use la_arena::Arena;
use std::collections::HashMap;
use syntax::{ArithOp, BinaryOp};

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
        vars: Arena::new(),
        constraints: Vec::new(),
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

    let mut resolved = HashMap::new();
    for &constraint in &ctx.constraints {
        match constraint {
            InferenceConstraint::IsType(tyvar, ty) => match ctx.analysis.types[ty] {
                Type::Unresolved(_) => {}
                _ => {
                    resolved.insert(tyvar, ty);
                }
            },
            InferenceConstraint::IsInteger(tyvar) => {
                // TODO obviously we don't want this to run in the wrong order
                if let Some(&ty) = resolved.get(&tyvar) {
                    assert!(matches!(ctx.analysis.types[ty], Type::Int(_, _)));
                }
            }
            InferenceConstraint::IsComparable(lhs, rhs) => {
                if let Some(&ty) = resolved.get(&lhs) {
                    resolved.insert(rhs, ty);
                }
                if let Some(&ty) = resolved.get(&rhs) {
                    resolved.insert(lhs, ty);
                }
            }
            InferenceConstraint::IsReturnType(idx) => {
                resolved.insert(idx, return_ty);
            }
        }
    }

    let mut modified = Vec::new();
    for (&expr, &expr_ty) in ctx.exprs.iter() {
        if let Type::Unresolved(idx) = ctx.analysis.types[expr_ty] {
            if let Some(&ty) = resolved.get(&idx) {
                modified.push((expr, ty));
            }
        }
    }
    ctx.exprs.extend(modified);

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
    vars: Arena<()>,
    constraints: Vec<InferenceConstraint>,
}

impl InferCtx<'_> {
    fn tyvar_of(&mut self, ty: TypeId) -> TypeVarId {
        match &self.analysis.types[ty] {
            &Type::Unresolved(idx) => idx,
            _ => {
                let tyvar = self.vars.alloc(());
                self.constraints
                    .push(InferenceConstraint::IsType(tyvar, ty));
                tyvar
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum InferenceConstraint {
    IsType(TypeVarId, TypeId),
    IsInteger(TypeVarId),
    IsComparable(TypeVarId, TypeVarId),
    IsReturnType(TypeVarId),
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
                    &ItemId::Function(func) => match &ctx.items[func].name {
                        Name::Present(func_name) if func_name == name => Some(func),
                        _ => None,
                    },
                    ItemId::Record(_) => None,
                    ItemId::Const(_) => None,
                    ItemId::Enum(_) => None,
                })
                .map(|func| {
                    let func = &ctx.items[func];
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
        Expr::Number(_) => {
            let tyvar = ctx.vars.alloc(());
            ctx.constraints.push(InferenceConstraint::IsInteger(tyvar));
            ctx.analysis.intern_type(Type::Unresolved(tyvar))
        }
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
        &Expr::Binary {
            op: BinaryOp::Cmp(_),
            lhs,
            rhs,
        } => {
            let lhs_ty = infer_expr(ctx, lhs);
            let rhs_ty = infer_expr(ctx, rhs);
            let lhs_tyvar = ctx.tyvar_of(lhs_ty);
            let rhs_tyvar = ctx.tyvar_of(rhs_ty);
            ctx.constraints
                .push(InferenceConstraint::IsComparable(lhs_tyvar, rhs_tyvar));
            ctx.analysis.intern_type(Type::Bool)
        }
        &Expr::Binary {
            op:
                BinaryOp::Arith(
                    ArithOp::Add
                    | ArithOp::Sub
                    | ArithOp::Mul
                    | ArithOp::Div
                    | ArithOp::Rem
                    | ArithOp::And
                    | ArithOp::Or
                    | ArithOp::Xor
                    | ArithOp::Shl
                    | ArithOp::Shr,
                ),
            lhs,
            rhs,
        } => {
            let lhs_ty = infer_expr(ctx, lhs);
            let rhs_ty = infer_expr(ctx, rhs);
            let lhs_tyvar = ctx.tyvar_of(lhs_ty);
            let rhs_tyvar = ctx.tyvar_of(rhs_ty);
            ctx.constraints
                .push(InferenceConstraint::IsType(lhs_tyvar, rhs_ty));
            ctx.constraints
                .push(InferenceConstraint::IsType(rhs_tyvar, lhs_ty));
            ctx.analysis.intern_type(Type::Bool)
        }
        &Expr::Binary { op: _, lhs, rhs } => {
            let lhs_ty = infer_expr(ctx, lhs);
            let _rhs_ty = infer_expr(ctx, rhs);
            lhs_ty
        }
        Expr::Break => ctx.analysis.intern_type(Type::Never),
        Expr::Continue => ctx.analysis.intern_type(Type::Never),
        &Expr::Return { value } => {
            let ty = infer_expr(ctx, value);
            let tyvar = ctx.tyvar_of(ty);
            ctx.constraints
                .push(InferenceConstraint::IsReturnType(tyvar));
            ctx.analysis.intern_type(Type::Never)
        }
        Expr::Call { callee, args } => {
            let callee_ty = infer_expr(ctx, *callee);
            let &Type::SpecificFn {
                ret_ty,
                ref param_tys,
                ..
            } = &ctx.analysis.types[callee_ty]
            else {
                eprintln!("called non-function type");
                return ctx.analysis.intern_type(Type::Error);
            };
            let param_tys = param_tys.clone();
            // TODO handle (here or elsewhere) the case where we've passed too many arguments
            for (i, &arg) in args.iter().enumerate() {
                let arg_ty = infer_expr(ctx, arg);
                let arg_tyvar = ctx.tyvar_of(arg_ty);
                ctx.constraints
                    .push(InferenceConstraint::IsType(arg_tyvar, param_tys[i]));
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
                        let record = &ctx.items[record_id];
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
                    let record = &ctx.items[record_id];
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
