use hir::{IntSize, Signed, TypeId};
use std::fmt::Write;
use syntax::{ArithOp, BinaryOp, CmpOp, UnaryOp};

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
    pub arg_tys: Vec<Type>,
    pub arg_regs: Vec<Reg>,
    pub vars: Vec<Type>,
    pub insts: Vec<Inst>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Reg(pub u32);

impl std::fmt::Debug for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}
#[derive(Clone, Copy)]
pub struct Var(pub u32);

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.0)
    }
}
#[derive(Clone, Copy)]
pub struct Func(pub u32);

impl std::fmt::Debug for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}", self.0)
    }
}

#[derive(Clone, Copy)]
pub struct Block(pub u32);

impl std::fmt::Debug for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b{}", self.0)
    }
}

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
    Call  {                     func: Func, args: Box<[Reg]> },
    Callv { ty: Type, dst: Reg, func: Func, args: Box<[Reg]> },
    Ret,
    Retv  { ty: Type, src: Reg },
    Br    { block: Block, args: Box<[Reg]> },
    Cbr   { cond: Reg, then_block: Block, then_args: Box<[Reg]>,
                       else_block: Block, else_args: Box<[Reg]> },
    Halt,
}

#[derive(Clone, Copy)]
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

impl std::fmt::Debug for Cmp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cmp::Eq => write!(f, "eq"),
            Cmp::Ne => write!(f, "ne"),
            Cmp::Ugt => write!(f, "ugt"),
            Cmp::Ult => write!(f, "ult"),
            Cmp::Ugte => write!(f, "ugte"),
            Cmp::Ulte => write!(f, "ulte"),
            Cmp::Sgt => write!(f, "sgt"),
            Cmp::Slt => write!(f, "slt"),
            Cmp::Sgte => write!(f, "sgte"),
            Cmp::Slte => write!(f, "slte"),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Type {
    Error,
    Int1,
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Error => write!(f, "error"),
            Type::Int1 => write!(f, "i1"),
            Type::Int8 => write!(f, "i8"),
            Type::Int16 => write!(f, "i16"),
            Type::Int32 => write!(f, "i32"),
            Type::Int64 => write!(f, "i64"),
            Type::Float32 => write!(f, "f32"),
            Type::Float64 => write!(f, "f64"),
        }
    }
}

struct Ctx<'a> {
    analysis: &'a hir::Analysis,
    _function: &'a hir::Function,
    body: &'a hir::Body,
    inference: &'a hir::InferenceResult,
    funcs: Vec<FuncData>,
    blocks: Vec<BlockData>,
    cur_block: Option<Block>,
    _next_var: u32,
    next_reg: u32,
    items: &'a hir::Items,
}

impl Ctx<'_> {
    fn _var(&mut self) -> Var {
        let var = Var(self._next_var);
        self._next_var += 1;
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
        for param_ty in self.inference.param_tys.iter() {
            let param_ty = self.lower_ty(*param_ty);
            let reg = self.reg();
            self.blocks[entry.0 as usize].arg_tys.push(param_ty);
            self.blocks[entry.0 as usize].arg_regs.push(reg);
        }
        self.switch_to_block(entry);
        self.lower_expr(self.body.expr);
        Function {
            funcs: self.funcs,
            blocks: self.blocks,
        }
    }

    fn lower_expr(&mut self, expr: hir::ExprId) -> Option<Reg> {
        match &self.body.exprs[expr] {
            hir::Expr::Missing => None,
            hir::Expr::Unit => None,
            hir::Expr::Name(name) => {
                let param_index = self
                    .body
                    .param_names
                    .iter()
                    .enumerate()
                    .find(|&(_, it)| it == name.as_str())
                    .unwrap()
                    .0;
                let entry_block = &self.blocks[0];
                Some(entry_block.arg_regs[param_index])
            }
            &hir::Expr::Number(value) => {
                let reg = self.reg();
                let ty = self.type_of(expr);
                self.push(Inst::Const {
                    ty,
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
                self.push(Inst::Br {
                    block: else_block,
                    args: Box::new([]),
                });
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
                self.push(Inst::Br {
                    block: join_block,
                    args: Box::new([]),
                });
                self.switch_to_block(else_block);
                self.lower_expr(else_expr);
                self.push(Inst::Br {
                    block: join_block,
                    args: Box::new([]),
                });
                self.switch_to_block(join_block);
                None
            }
            &hir::Expr::Loop { body } => {
                let start = self.block();
                self.lower_expr(body);
                self.push(Inst::Br {
                    block: start,
                    args: Box::new([]),
                });
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
            &hir::Expr::Unary { op, operand } => {
                let ty = self.type_of(operand);
                let operand = self.lower_expr(operand).unwrap();
                let dst = self.reg();
                match op {
                    UnaryOp::Not => {
                        let ones = self.reg();
                        let constant = match ty {
                            Type::Int1 => 1 as u64,
                            Type::Int8 => !0u8 as u64,
                            Type::Int16 => !0u16 as u64,
                            Type::Int32 => !0u32 as u64,
                            Type::Int64 => !0u64 as u64,
                            Type::Error | Type::Float32 | Type::Float64 => todo!(),
                        };
                        self.push(Inst::Const {
                            ty,
                            dst: ones,
                            value: constant,
                        });
                        self.push(Inst::Xor {
                            ty,
                            dst,
                            lhs: ones,
                            rhs: operand,
                        });
                    }
                    UnaryOp::Neg => {
                        let zero = self.reg();
                        self.push(Inst::Const {
                            ty,
                            dst: zero,
                            value: 0,
                        });
                        self.push(Inst::Isub {
                            ty,
                            dst,
                            lhs: zero,
                            rhs: operand,
                        });
                    }
                    UnaryOp::Ref => todo!(),
                    UnaryOp::Deref => todo!(),
                }
                Some(dst)
            }
            &hir::Expr::Binary { op, lhs, rhs } => {
                let ty = self.type_of(lhs);
                let lhs = self.lower_expr(lhs).unwrap();
                let rhs = self.lower_expr(rhs).unwrap();
                let dst = self.reg();
                self.push(bin_op(op, ty, dst, lhs, rhs));
                Some(dst)
            }
            hir::Expr::Break => todo!(),
            hir::Expr::Continue => todo!(),
            &hir::Expr::Return { value } => {
                let hir_ty_id = self.inference.exprs[&value];
                let hir_ty = &self.analysis[hir_ty_id];
                match hir_ty {
                    hir::Type::Unit => {
                        self.push(Inst::Ret);
                        None
                    }
                    _ => {
                        let ty = self.type_of(value);
                        let value = self.lower_expr(value).unwrap();
                        self.push(Inst::Retv { ty, src: value });
                        None
                    }
                }
            }
            hir::Expr::Call { callee, args } => {
                let hir::Type::SpecificFn {
                    name: hir::Name::Present(name),
                    ret_ty,
                    param_tys,
                } = &self.analysis[self.inference.exprs[&callee]]
                else {
                    todo!()
                };
                let arg_regs = args
                    .iter()
                    .map(|&arg| self.lower_expr(arg).unwrap())
                    .collect();
                if self.analysis[*ret_ty] == hir::Type::Unit {
                    let func = Func(self.funcs.len() as u32);
                    self.funcs.push(FuncData {
                        name: name.clone(),
                        ret: None,
                        args: self.lower_tys(param_tys),
                    });
                    self.push(Inst::Call {
                        func,
                        args: arg_regs,
                    });
                    None
                } else {
                    let ret_ty = self.lower_ty(*ret_ty);
                    let func = Func(self.funcs.len() as u32);
                    self.funcs.push(FuncData {
                        name: name.clone(),
                        ret: Some(ret_ty),
                        args: self.lower_tys(param_tys),
                    });
                    let dst = self.reg();
                    self.push(Inst::Callv {
                        ty: ret_ty,
                        dst,
                        func,
                        args: arg_regs,
                    });
                    Some(dst)
                }
            }
            hir::Expr::Index { base: _, index: _ } => todo!(),
            hir::Expr::Field { base, name } => {
                let hir_ty = self.inference.exprs[base];
                let value = self.lower_expr(*base).unwrap();
                let hir::Type::Ptr(hir_indirect_ty) = self.analysis[hir_ty] else {
                    todo!();
                };
                let hir::Type::Record(record_id) = self.analysis[hir_indirect_ty] else {
                    todo!();
                };
                let record = &self.items[record_id];
                let (field_index, _field) = record
                    .fields
                    .iter()
                    .enumerate()
                    .find(|(_, field)| field.name == *name.as_str())
                    .unwrap();
                assert_eq!(field_index, 0);

                Some(value)
            }
        }
    }

    fn type_of(&self, lhs: hir::ExprId) -> Type {
        self.lower_ty(self.inference.exprs[&lhs])
    }

    fn lower_tys(&self, tys: &[TypeId]) -> Vec<Type> {
        tys.iter().map(|&ty| self.lower_ty(ty)).collect()
    }

    fn lower_ty(&self, ty: TypeId) -> Type {
        match &self.analysis[ty] {
            hir::Type::Error => Type::Error,
            hir::Type::Never => Type::Error,
            hir::Type::Unit => todo!(),
            hir::Type::Bool => Type::Int1,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size8) => Type::Int8,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size16) => Type::Int16,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size32) => Type::Int32,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size64) => Type::Int64,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::SizePtr) => Type::Int64,
            hir::Type::Ptr(_) => Type::Int64,
            hir::Type::SpecificFn {
                ret_ty: _,
                param_tys: _,
                name: _,
            } => todo!(),
            hir::Type::GenericFn {
                ret_ty: _,
                param_tys: _,
            } => todo!(),
            hir::Type::Record(_) => Type::Error,
            hir::Type::Enum(_) => todo!(),
            hir::Type::Unresolved(_) => Type::Error,
        }
    }
}

fn bin_op(op: BinaryOp, ty: Type, dst: Reg, lhs: Reg, rhs: Reg) -> Inst {
    match op {
        BinaryOp::Asg(_) => todo!(),
        BinaryOp::Cmp(cmp) => Inst::Icmp {
            ty,
            dst,
            lhs,
            rhs,
            cmp: match cmp {
                CmpOp::Eq => Cmp::Eq,
                CmpOp::Ne => Cmp::Ne,
                CmpOp::Lt => Cmp::Slt,
                CmpOp::Lte => Cmp::Slte,
                CmpOp::Gt => Cmp::Sgt,
                CmpOp::Gte => Cmp::Sgte,
            },
        },
        BinaryOp::Arith(ArithOp::Add) => Inst::Iadd { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Sub) => Inst::Isub { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Mul) => Inst::Imul { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Div) => Inst::Sdiv { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Rem) => Inst::Srem { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::And) => Inst::And { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Or) => Inst::Or { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Xor) => Inst::Xor { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Shl) => Inst::Shl { ty, dst, lhs, rhs },
        BinaryOp::Arith(ArithOp::Shr) => Inst::Lshr { ty, dst, lhs, rhs },
        BinaryOp::Logic(_) => todo!(),
    }
}

pub fn lower(
    analysis: &hir::Analysis,
    items: &hir::Items,
    function: &hir::Function,
    body: &hir::Body,
    inference: &hir::InferenceResult,
) -> Function {
    let ctx = Ctx {
        analysis,
        items,
        _function: function,
        body,
        inference,
        funcs: Vec::new(),
        blocks: Vec::new(),
        cur_block: None,
        _next_var: 0,
        next_reg: 0,
    };
    ctx.lower_function()
}

pub fn print_function(function: &Function) -> String {
    let mut s = String::new();
    print_function_(&mut s, function);
    s
}

fn print_function_(s: &mut String, function: &Function) {
    for (i, block) in function.blocks.iter().enumerate() {
        s.push('b');
        _ = write!(s, "{i}");
        if !block.arg_regs.is_empty() {
            s.push('(');
            for (i, (reg, ty)) in block.arg_regs.iter().zip(block.arg_tys.iter()).enumerate() {
                if i != 0 {
                    s.push_str(", ");
                }
                _ = write!(s, "{reg:?} {ty:?}");
            }
            s.push(')');
        }
        s.push(':');
        s.push('\n');

        for inst in block.insts.iter() {
            _ = write!(s, "    ");
            print_inst(s, inst);
            _ = writeln!(s);
        }
    }
}

#[rustfmt::skip]
fn print_inst(s: &mut String, inst: &Inst) {
    match inst {
        Inst::Const { ty, dst, value } => _ =
            write!(s, "{dst:?} = const {ty:?} {value:?}"),
        Inst::Load { ty, dst, src } => _ =
            write!(s, "{dst:?} = load {ty:?} {src:?}"),
        Inst::Store { ty, dst, src } => _ =
            write!(s, "{dst:?} = store {ty:?} {src:?}"),
        Inst::Zext { ty, dst, operand } => _ =
            write!(s, "{dst:?} = zext {ty:?} {operand:?}"),
        Inst::Sext { ty, dst, operand } => _ =
            write!(s, "{dst:?} = sext {ty:?} {operand:?}"),
        Inst::Trunc { ty, dst, operand } => _ =
            write!(s, "{dst:?} = trunc {ty:?} {operand:?}"),
        Inst::Iadd { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = iadd {ty:?} {lhs:?} {rhs:?}"),
        Inst::Isub { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = isub {ty:?} {lhs:?} {rhs:?}"),
        Inst::Imul { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = imul {ty:?} {lhs:?} {rhs:?}"),
        Inst::Sdiv { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = sdiv {ty:?} {lhs:?} {rhs:?}"),
        Inst::Udiv { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = udiv {ty:?} {lhs:?} {rhs:?}"),
        Inst::Srem { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = srem {ty:?} {lhs:?} {rhs:?}"),
        Inst::Urem { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = urem {ty:?} {lhs:?} {rhs:?}"),
        Inst::Icmp { ty, dst, lhs, rhs, cmp } => _ =
            write!(s, "{dst:?} = cmp {cmp:?} {ty:?} {lhs:?} {rhs:?}"),
        Inst::Shl { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = shl {ty:?} {lhs:?} {rhs:?}"),
        Inst::Lshr { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = lshr {ty:?} {lhs:?} {rhs:?}"),
        Inst::Ashr { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = ashr {ty:?} {lhs:?} {rhs:?}"),
        Inst::And { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = and {ty:?} {lhs:?} {rhs:?}"),
        Inst::Or { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = or {ty:?} {lhs:?} {rhs:?}"),
        Inst::Xor { ty, dst, lhs, rhs } => _ =
            write!(s, "{dst:?} = xor {ty:?} {lhs:?} {rhs:?}"),
        Inst::Call { func, args } => _ =
            write!(s, "call {func:?} {args:?}"),
        Inst::Callv { dst, ty, func, args } => _ =
            write!(s, "{dst:?} = call {ty:?} {func:?} {args:?}"),
        Inst::Ret => _ =
            write!(s, "ret"),
        Inst::Retv { ty, src } => _ =
            write!(s, "ret {ty:?} {src:?}"),
        Inst::Br { block, args } => _ =
            write!(s, "br {block:?} {args:?}"),
        Inst::Cbr { cond, then_block, then_args, else_block, else_args } => _ =
            write!(s, "cbr {cond:?} {then_block:?} {then_args:?} {else_block:?} {else_args:?}"),
        Inst::Halt => _ =
            write!(s, "halt"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};
    use syntax::AstNode;

    fn check_inference(src: &str, expected: Expect) {
        let file = syntax::parse_file(src);
        let items = hir::file_items(file.clone());
        let mut analysis = hir::Analysis::default();
        let mut out = String::new();
        for item in items.items() {
            match item {
                &hir::ItemId::Function(func_id) => {
                    let func = &items[func_id];
                    let body = hir::lower_function_body(func.ast.to_node(file.syntax()));
                    let inference = hir::infer(&mut analysis, &items, func, &body);
                    for (expr_id, _) in body.exprs.iter() {
                        let Some(ptr) = body.expr_map.get(&expr_id) else {
                            continue;
                        };
                        let node = ptr.to_node(file.syntax());
                        let text = node.syntax().text();
                        let Some(type_id) = inference.exprs.get(&expr_id) else {
                            continue;
                        };
                        writeln!(
                            &mut out,
                            "{:?}: {}",
                            &text,
                            hir::print_type(&analysis, *type_id)
                        )
                        .unwrap();
                    }
                }
                hir::ItemId::Record(_) => {}
                hir::ItemId::Const(_) => {}
                hir::ItemId::Enum(_) => {}
            }
        }
        expected.assert_eq(&out);
    }

    fn check_codegen(src: &str, expected: Expect) {
        let file = syntax::parse_file(src);
        let items = hir::file_items(file.clone());
        let mut analysis = hir::Analysis::default();
        let mut out = String::new();
        for item in items.items() {
            match item {
                &hir::ItemId::Function(func_id) => {
                    let func = &items[func_id];
                    let body = hir::lower_function_body(func.ast.to_node(file.syntax()));
                    let inference = hir::infer(&mut analysis, &items, func, &body);
                    let func = lower(&analysis, &items, &func, &body, &inference);
                    out.push_str(&print_function(&func));
                }
                hir::ItemId::Record(_) => {}
                hir::ItemId::Const(_) => {}
                hir::ItemId::Enum(_) => {}
            }
        }
        expected.assert_eq(&out);
    }

    #[test]
    fn field_access() {
        check_inference(
            "
struct Vec2 {
    x u32
    y u32
}

fn get_x(v ptr Vec2) { return v.x }",
            expect![[r#"
                "v": ptr record Idx::<Record>(0)
                "v.x": u32
                "return v.x": (never)
                "{ return v.x }": (unit)
            "#]],
        );
        check_codegen(
            "
struct Vec2 {
    x u32
    y u32
}

fn get_x(v ptr Vec2) { return v.x }",
            expect![[r#"
                b0(%0 i64):
                    ret i32 %0
            "#]],
        );
    }

    #[test]
    fn recursive_function() {
        check_inference(
            "
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}
",
            expect![[r#"
                "n": u32
                "1": u32
                "n <= 1": bool
                "1": u32
                "return 1": (never)
                "{ return 1 }": (unit)
                "if n <= 1 { return 1 }": (unit)
                "fib": Type::SpecificFn
                "n": u32
                "1": u32
                "n - 1": bool
                "fib(n - 1)": u32
                "fib": Type::SpecificFn
                "n": u32
                "2": u32
                "n - 2": bool
                "fib(n - 2)": u32
                "fib(n - 1) + fib(n - 2)": bool
                "return fib(n - 1) + fib(n - 2)": (never)
                "{\n    if n <= 1 { return 1 }\n    return fib(n - 1) + fib(n - 2)\n}": (unit)
            "#]],
        );
        check_codegen(
            "
fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}
",
            expect![[r#"
                b0(%0 i32):
                    %1 = const i32 1
                    %2 = cmp slte i32 %0 %1
                    cbr %2 b1 [] b2 []
                b1:
                    %3 = const i32 1
                    ret i32 %3
                    br b2 []
                b2:
                    %4 = const i32 1
                    %5 = isub i32 %0 %4
                    %6 = call i32 f0 [%5]
                    %7 = const i32 2
                    %8 = isub i32 %0 %7
                    %9 = call i32 f1 [%8]
                    %10 = iadd i32 %6 %9
                    ret i1 %10
            "#]],
        );
        check_codegen(
            "
fn fib(n u64) u64 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}
",
            expect![[r#"
                b0(%0 i64):
                    %1 = const i64 1
                    %2 = cmp slte i64 %0 %1
                    cbr %2 b1 [] b2 []
                b1:
                    %3 = const i64 1
                    ret i64 %3
                    br b2 []
                b2:
                    %4 = const i64 1
                    %5 = isub i64 %0 %4
                    %6 = call i64 f0 [%5]
                    %7 = const i64 2
                    %8 = isub i64 %0 %7
                    %9 = call i64 f1 [%8]
                    %10 = iadd i64 %6 %9
                    ret i1 %10
            "#]],
        );
    }

    #[test]
    fn function_call() {
        check_inference(
            "
fn exit(n i32)
fn do_exit() { exit(0) }
",
            expect![[r#"
                "exit": Type::SpecificFn
                "0": i32
                "exit(0)": (unit)
                "{ exit(0) }": (unit)
            "#]],
        );
        check_codegen(
            "
fn exit(n i32)
fn do_exit() { exit(0) }
",
            expect![[r#"
                b0(%0 i32):
                b0:
                    %0 = const i32 0
                    call f0 [%0]
            "#]],
        );
    }

    #[test]
    fn bitwise_ops() {
        check_codegen(
            "
fn double(x i32) { return x + x }
fn square(x i32) { return x * x }
fn negate(x i32) { return -x }
fn complement(x i32) { return !x }
fn bitand(x i32, y i32) { return x & y }
fn bitor(x i32, y i32) { return x | y }
fn bitxor(x i32, y i32) { return x ^ y }
",
            expect![[r#"
                b0(%0 i32):
                    %1 = iadd i32 %0 %0
                    ret i1 %1
                b0(%0 i32):
                    %1 = imul i32 %0 %0
                    ret i1 %1
                b0(%0 i32):
                    %2 = const i32 0
                    %1 = isub i32 %2 %0
                    ret i32 %1
                b0(%0 i32):
                    %2 = const i32 4294967295
                    %1 = xor i32 %2 %0
                    ret i32 %1
                b0(%0 i32, %1 i32):
                    %2 = and i32 %0 %1
                    ret i1 %2
                b0(%0 i32, %1 i32):
                    %2 = or i32 %0 %1
                    ret i1 %2
                b0(%0 i32, %1 i32):
                    %2 = xor i32 %0 %1
                    ret i1 %2
            "#]],
        )
    }
}
