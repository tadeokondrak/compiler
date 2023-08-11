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

#[derive(Clone, Copy)]
pub struct Reg(u32);

impl std::fmt::Debug for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}
#[derive(Clone, Copy)]
pub struct Var(u32);

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.0)
    }
}
#[derive(Clone, Copy)]
pub struct Func(u32);

impl std::fmt::Debug for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}", self.0)
    }
}

#[derive(Clone, Copy)]
pub struct Block(u32);

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
    Br    { block: Block },
    Cbr   { cond: Reg, then_block: Block, then_args: Box<[Reg]>,
                       else_block: Block, else_args: Box<[Reg]> },
    Halt,
}

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
    function: &'a hir::Function,
    body: &'a hir::Body,
    inference: &'a hir::InferenceResult,
    funcs: Vec<FuncData>,
    blocks: Vec<BlockData>,
    cur_block: Option<Block>,
    next_var: u32,
    next_reg: u32,
    items: &'a hir::Items,
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
            hir::Expr::Unit => todo!(),
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
            &hir::Expr::Unary { op, operand } => {
                let ty = self.type_of(operand);
                let operand = self.lower_expr(operand).unwrap();
                let dst = self.reg();
                match op {
                    UnaryOp::Not => todo!(),
                    UnaryOp::Neg => todo!(),
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
            hir::Expr::Index { base, index } => todo!(),
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
            hir::Type::Never => todo!(),
            hir::Type::Unit => todo!(),
            hir::Type::Bool => Type::Int1,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size8) => Type::Int8,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size16) => Type::Int16,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size32) => Type::Int32,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::Size64) => Type::Int64,
            hir::Type::Int(Signed::Yes | Signed::No, IntSize::SizePtr) => Type::Int64,
            hir::Type::Ptr(_) => Type::Int64,
            hir::Type::SpecificFn {
                ret_ty,
                param_tys,
                name,
            } => todo!(),
            hir::Type::GenericFn { ret_ty, param_tys } => todo!(),
            hir::Type::Record(_) => Type::Error,
            hir::Type::Enum(_) => todo!(),
        }
    }
}

#[rustfmt::skip]
fn bin_op(op: BinaryOp, ty: Type, dst: Reg, lhs: Reg, rhs: Reg) -> Inst {
    match op {
        BinaryOp::Asg(_) => todo!(),
        BinaryOp::Cmp(CmpOp::Eq) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Eq },
        BinaryOp::Cmp(CmpOp::Ne) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Ne },
        BinaryOp::Cmp(CmpOp::Lt) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Slt },
        BinaryOp::Cmp(CmpOp::Lte) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Slte },
        BinaryOp::Cmp(CmpOp::Gt) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Sgt },
        BinaryOp::Cmp(CmpOp::Gte) => Inst::Icmp { ty, dst, lhs, rhs, cmp: Cmp::Sgte },
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
        function,
        body,
        inference,
        funcs: Vec::new(),
        blocks: Vec::new(),
        cur_block: None,
        next_var: 0,
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
                    s.push(',');
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
        Inst::Br { block } => _ =
            write!(s, "br {block:?}"),
        Inst::Cbr { cond, then_block, then_args, else_block, else_args } => _ =
            write!(s, "cbr {cond:?} {then_block:?} {then_args:?} {else_block:?} {else_args:?}"),
        Inst::Halt => _ =
            write!(s, "halt"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syntax::AstNode;

    #[test]
    fn test_infer() {
        let file = syntax::parse_file(
            "
struct Vec2 {
    x u32
    y u32
}
fn get_x(v ptr Vec2) { return v.x }

fn exit(n i32)

fn fib(n u32) u32 {
    if n <= 1 { return 1 }
    exit(0)
    return fib(n - 1) + fib(n - 2)
}",
        );
        let items = hir::file_items(file.clone());
        let mut analysis = hir::Analysis::default();
        for item in items.items() {
            match item {
                &hir::ItemId::Function(func_id) => {
                    let func = &items[func_id];
                    let body = hir::lower_function_body(func.ast.to_node(file.syntax()));
                    eprintln!("{}", hir::print_function(&func, &body));
                    let inference = hir::infer(&mut analysis, &items, func, &body);
                    let mut inference_text = String::new();
                    for (expr_id, _) in body.exprs.iter() {
                        let Some(ptr) = body.expr_map.get(&expr_id) else {
                            continue;
                        };
                        let node = ptr.to_node(file.syntax());
                        let text = node.syntax().text();
                        let Some(type_id) = inference.exprs.get(&expr_id) else {
                            continue;
                        };
                        _ = writeln!(
                            &mut inference_text,
                            "{:?}: {}",
                            &text,
                            hir::print_type(&analysis, *type_id)
                        );
                    }
                    eprintln!("{inference_text}");
                    let func = lower(&analysis, &items, &func, &body, &inference);
                    eprintln!("{}", print_function(&func));
                }
                hir::ItemId::Record(_) => {}
                hir::ItemId::Const(_) => {}
                hir::ItemId::Enum(_) => {}
            }
        }
    }
}
