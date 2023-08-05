#[derive(Debug)]
pub struct Function {
    pub funcs: Vec<FuncData>,
    pub blocks: Vec<BlockData>,
}

#[derive(Debug)]
pub struct FuncData {
    pub name: String,
    pub ret: Option<Type>,
    pub args: Vec<Type>,
}

#[derive(Debug, Default)]
pub struct BlockData {
    pub args: Vec<Type>,
    pub vars: Vec<Type>,
    pub insts: Vec<Inst>,
}

#[derive(Debug, Clone, Copy)]
pub struct Reg(u32);
#[derive(Debug, Clone, Copy)]
pub struct Var(u32);
#[derive(Debug, Clone, Copy)]
pub struct Func(u32);
#[derive(Debug, Clone, Copy)]
pub struct Block(u32);

#[rustfmt::skip]
#[derive(Debug)]
pub enum Inst {
    Const { ty: Type, dst: Reg, value: u64 },
    Load  { ty: Type, dst: Reg, src: Var },
    Store { ty: Type, dst: Var, src: Reg },
    Zext  { ty: Type, dst: Reg, operand: Reg },
    Sext  { ty: Type, dst: Reg, operand: Reg },
    Trunc { ty: Type, dst: Reg, operand: Reg },
    Iadd  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Isub  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Imul  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Sdiv  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Udiv  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Srem  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Urem  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Icmp  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg, cmp: Cmp },
    Shl   { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Lshr  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Ashr  { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    And   { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Or    { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Xor   { ty: Type, dst: Reg, lhs: Reg, rhs: Reg },
    Call  {           func: Func, args: Box<[Reg]> },
    Callv { ty: Type, func: Func, args: Box<[Reg]> },
    Ret,
    Retv  { ty: Type, src: Reg },
    Br    { block: Block },
    Cbr   { cond: Reg, then_block: Block, then_args: Box<[Reg]>,
                       else_block: Block, else_args: Box<[Reg]> },
    Halt,
}

#[derive(Debug)]
pub enum Cmp {
    Eq,
    Ne,
    Ugt,
    Ult,
    Ugte,
    Ulte,
    Sgt,
    Slt,
    Sgte,
    Slte,
}

#[derive(Debug)]
pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
}

struct Ctx<'a> {
    db: &'a hir::Db,
    function: &'a hir::Function,
    inference: &'a hir::InferenceResult,
    funcs: Vec<FuncData>,
    blocks: Vec<BlockData>,
    cur_block: Option<Block>,
    next_var: u32,
    next_reg: u32,
}
impl Ctx<'_> {
    fn var(&mut self) -> Var {
        let var = Var(self.next_var);
        self.next_var += 1;
        var
    }

    fn reg(&mut self) -> Reg {
        let reg = Reg(self.next_reg);
        self.next_reg += 1;
        reg
    }

    fn block(&mut self) -> Block {
        let block = Block(self.blocks.len() as u32);
        self.blocks.push(BlockData::default());
        block
    }

    fn switch_to_block(&mut self, block: Block) {
        self.cur_block = Some(block);
    }

    fn push(&mut self, inst: Inst) {
        let block = self.cur_block.unwrap();
        self.blocks[block.0 as usize].insts.push(inst);
    }

    fn lower_function(mut self) -> Function {
        let entry = self.block();
        self.switch_to_block(entry);
        self.lower_expr(self.function.body.expr);
        Function {
            funcs: self.funcs,
            blocks: self.blocks,
        }
    }

    fn lower_expr(&mut self, expr: hir::ExprId) -> Option<Reg> {
        match &self.function.body.exprs[expr] {
            hir::Expr::Missing => todo!(),
            hir::Expr::Unit => todo!(),
            hir::Expr::Name(_) => {
                // TODO
                let reg = self.reg();
                self.push(Inst::Const {
                    ty: Type::Int32,
                    dst: reg,
                    value: 0,
                });
                Some(reg)
            }
            &hir::Expr::Number(value) => {
                let reg = self.reg();
                self.push(Inst::Const {
                    ty: Type::Int32,
                    dst: reg,
                    value,
                });
                Some(reg)
            }
            &hir::Expr::If {
                cond,
                then_expr,
                else_expr: None,
            } => {
                let cond = self.lower_expr(cond).unwrap();
                let then_block = self.block();
                let else_block = self.block();
                self.push(Inst::Cbr {
                    cond,
                    then_block,
                    then_args: Box::new([]),
                    else_block,
                    else_args: Box::new([]),
                });
                self.switch_to_block(then_block);
                self.lower_expr(then_expr);
                self.push(Inst::Br { block: else_block });
                self.switch_to_block(else_block);
                None
            }
            &hir::Expr::If {
                cond,
                then_expr,
                else_expr: Some(else_expr),
            } => {
                let cond = self.lower_expr(cond).unwrap();
                let then_block = self.block();
                let else_block = self.block();
                let join_block = self.block();
                self.push(Inst::Cbr {
                    cond,
                    then_block,
                    then_args: Box::new([]),
                    else_block,
                    else_args: Box::new([]),
                });
                self.switch_to_block(then_block);
                self.lower_expr(then_expr);
                self.push(Inst::Br { block: join_block });
                self.switch_to_block(else_block);
                self.lower_expr(else_expr);
                self.push(Inst::Br { block: join_block });
                self.switch_to_block(join_block);
                None
            }
            &hir::Expr::Loop { body } => {
                let start = self.block();
                self.lower_expr(body);
                self.push(Inst::Br { block: start });
                None
            }
            hir::Expr::Block { body } => {
                for stmt in body.iter() {
                    match stmt {
                        &hir::Stmt::Let(_, _) => todo!(),
                        &hir::Stmt::Expr(it) => {
                            self.lower_expr(it);
                        }
                    }
                }
                None
            }
            hir::Expr::Unary { op, operand } => todo!(),
            &hir::Expr::Binary { op, lhs, rhs } => {
                let ty = self.type_of(lhs);
                let lhs = self.lower_expr(lhs).unwrap();
                let rhs = self.lower_expr(rhs).unwrap();
                let dst = self.reg();
                self.push(match op {
                    hir::BinaryOp::Add => Inst::Iadd { ty, dst, lhs, rhs },
                    hir::BinaryOp::Sub => Inst::Isub { ty, dst, lhs, rhs },
                    hir::BinaryOp::Lte => Inst::Icmp {
                        ty,
                        cmp: Cmp::Slte,
                        dst,
                        lhs,
                        rhs,
                    },
                });
                Some(dst)
            }
            hir::Expr::Break => todo!(),
            hir::Expr::Continue => todo!(),
            &hir::Expr::Return { value } => {
                let ty = self.type_of(value);
                let value = self.lower_expr(value).unwrap();
                self.push(Inst::Retv { ty, src: value });
                None
            }
            hir::Expr::Call { callee, args } => {
                let hir::Type::Fn { ret_ty, param_tys } = &self.db[self.inference.exprs[callee]] else {
                    todo!()
                };
                for &arg in args.iter() {
                    self.lower_expr(arg);
                }
                // TODO
                Some(Reg(!0))
            }
            hir::Expr::Index { base, index } => todo!(),
            hir::Expr::Field { base, name } => todo!(),
        }
    }

    fn type_of(&self, lhs: hir::ExprId) -> Type {
        match &self.db[self.inference.exprs[&lhs]] {
            hir::Type::Error => todo!(),
            hir::Type::Never => todo!(),
            hir::Type::Unit => todo!(),
            hir::Type::Uint32 => Type::Int32,
            hir::Type::Ptr(_) => todo!(),
            hir::Type::Fn { ret_ty, param_tys } => todo!(),
        }
    }
}

fn lower(db: &hir::Db, function: &hir::Function, inference: &hir::InferenceResult) -> Function {
    let ctx = Ctx {
        db,
        function,
        inference,
        funcs: Vec::new(),
        blocks: Vec::new(),
        cur_block: None,
        next_var: 0,
        next_reg: 0,
    };
    ctx.lower_function()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let file = syntax::parse_file(
            "
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = hir::items(file.clone());
        let mut db = hir::Db::default();
        for item in items.items().values() {
            match item {
                hir::Item::Function(func) => {
                    let inference = hir::infer(&mut db, &items, func);
                    let function = lower(&db, &func, &inference);
                    dbg!(function);
                }
            }
        }
    }
}
