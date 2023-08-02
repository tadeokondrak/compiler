pub struct Function {
    pub funcs: Vec<FuncData>,
    pub blocks: Vec<BlockData>,
}

pub struct FuncData {
    pub name: String,
    pub ret: Option<Type>,
    pub args: Vec<Type>,
}

pub struct BlockData {
    pub args: Vec<Type>,
    pub vars: Vec<Type>,
    pub insts: Vec<Inst>,
}

pub struct Reg(u32);
pub struct Var(u32);
pub struct Func(u32);
pub struct Block(u32);

#[rustfmt::skip]
pub enum Inst {
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

pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
}
