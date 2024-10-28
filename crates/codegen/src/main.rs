use cranelift_codegen::{
    ir::{self, condcodes::IntCC, types, AbiParam, InstBuilder, MemFlags, Signature},
    isa::CallConv,
    settings::Configurable,
    Context,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{default_libcall_names, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::{BTreeMap, HashMap};
use syntax::AstNode;

fn cl_ty(ty: mir::Type) -> types::Type {
    match ty {
        mir::Type::Error => panic!(),
        mir::Type::Int1 => types::I8,
        mir::Type::Int8 => types::I8,
        mir::Type::Int16 => types::I16,
        mir::Type::Int32 => types::I32,
        mir::Type::Int64 => types::I64,
        mir::Type::Float32 => types::F32,
        mir::Type::Float64 => types::F64,
    }
}

fn cl_var(src: mir::Var) -> Variable {
    Variable::from_u32(src.0)
}

fn gen_function(
    module: &mut dyn Module,
    mir_func: mir::Function,
    builder: &mut FunctionBuilder,
    func_ids: &HashMap<String, FuncId>,
) {
    let cl_blocks = mir_func
        .blocks
        .iter()
        .map(|_| builder.create_block())
        .collect::<Vec<_>>();
    let mut regs = BTreeMap::new();

    for (i, block) in mir_func.blocks.iter().enumerate() {
        builder.switch_to_block(cl_blocks[i]);
        for j in 0..block.arg_regs.len() {
            let reg = block.arg_regs[j];
            let ty = block.arg_tys[j];
            let val = builder.append_block_param(cl_blocks[i], cl_ty(ty));
            regs.insert(reg, val);
        }
        for inst in &block.insts {
            match *inst {
                mir::Inst::Const { ty, dst, value } => {
                    let val = match ty {
                        mir::Type::Error => panic!(),
                        mir::Type::Int1 => builder.ins().iconst(types::I8, value as i64),
                        mir::Type::Int8 => builder.ins().iconst(types::I8, value as i64),
                        mir::Type::Int16 => builder.ins().iconst(types::I16, value as i64),
                        mir::Type::Int32 => builder.ins().iconst(types::I32, value as i64),
                        mir::Type::Int64 => builder.ins().iconst(types::I64, value as i64),
                        mir::Type::Float32 => builder.ins().f32const(f32::from_bits(value as u32)),
                        mir::Type::Float64 => builder.ins().f64const(f64::from_bits(value)),
                    };
                    regs.insert(dst, val);
                }
                mir::Inst::Load { ty, dst, src } => {
                    let src = builder.use_var(cl_var(src));
                    let val = builder.ins().load(cl_ty(ty), MemFlags::new(), src, 0);
                    regs.insert(dst, val);
                }
                mir::Inst::Store { ty, dst, src } => {
                    builder.declare_var(cl_var(dst), cl_ty(ty));
                    builder.def_var(cl_var(dst), regs[&src]);
                }
                mir::Inst::Zext { ty, dst, operand } => {
                    let val = builder.ins().uextend(cl_ty(ty), regs[&operand]);
                    regs.insert(dst, val);
                }
                mir::Inst::Sext { ty, dst, operand } => {
                    let val = builder.ins().sextend(cl_ty(ty), regs[&operand]);
                    regs.insert(dst, val);
                }
                mir::Inst::Trunc {
                    ty: _,
                    dst,
                    operand,
                } => {
                    regs.insert(dst, regs[&operand]);
                }
                mir::Inst::Iadd {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().iadd(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Isub {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().isub(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Imul {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().imul(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Sdiv {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().sdiv(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Udiv {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().udiv(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Srem {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().srem(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Urem {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().urem(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Icmp {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                    cmp,
                } => {
                    let cond = match cmp {
                        mir::Cmp::Eq => IntCC::Equal,
                        mir::Cmp::Ne => IntCC::NotEqual,
                        mir::Cmp::Ugt => IntCC::UnsignedGreaterThan,
                        mir::Cmp::Ult => IntCC::UnsignedLessThan,
                        mir::Cmp::Ugte => IntCC::UnsignedGreaterThanOrEqual,
                        mir::Cmp::Ulte => IntCC::UnsignedLessThanOrEqual,
                        mir::Cmp::Sgt => IntCC::SignedGreaterThan,
                        mir::Cmp::Slt => IntCC::SignedLessThan,
                        mir::Cmp::Sgte => IntCC::SignedGreaterThanOrEqual,
                        mir::Cmp::Slte => IntCC::SignedLessThanOrEqual,
                    };
                    let val = builder.ins().icmp(cond, regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Shl {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().ishl(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Lshr {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().ushr(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Ashr {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().sshr(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::And {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().band(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Or {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().bor(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Xor {
                    ty: _,
                    dst,
                    lhs,
                    rhs,
                } => {
                    let val = builder.ins().bxor(regs[&lhs], regs[&rhs]);
                    regs.insert(dst, val);
                }
                mir::Inst::Call { func, ref args } => {
                    let func_data = &mir_func.funcs[func.0 as usize];
                    let func = module.declare_func_in_func(func_ids[&func_data.name], builder.func);
                    builder.ins().call(func, &cl_args(&args, &regs));
                }
                mir::Inst::Callv {
                    ty: _,
                    dst,
                    func,
                    ref args,
                } => {
                    let func_data = &mir_func.funcs[func.0 as usize];
                    let func = module.declare_func_in_func(func_ids[&func_data.name], builder.func);
                    let inst = builder.ins().call(func, &cl_args(&args, &regs));
                    let val = builder.inst_results(inst)[0];
                    regs.insert(dst, val);
                }
                mir::Inst::Ret => {
                    builder.ins().return_(&[]);
                    break;
                }
                mir::Inst::Retv { ty: _, src } => {
                    builder.ins().return_(&[regs[&src]]);
                    break;
                }
                mir::Inst::Br { block, ref args } => {
                    builder
                        .ins()
                        .jump(cl_block(&cl_blocks, block), &cl_args(args, &regs));
                    break;
                }
                mir::Inst::Cbr {
                    cond,
                    then_block,
                    ref then_args,
                    else_block,
                    ref else_args,
                } => {
                    builder.ins().brif(
                        regs[&cond],
                        cl_block(&cl_blocks, then_block),
                        &cl_args(then_args, &regs),
                        cl_block(&cl_blocks, else_block),
                        &cl_args(else_args, &regs),
                    );
                    break;
                }
                mir::Inst::Halt => {
                    builder.ins().trap(ir::TrapCode::user(1).unwrap());
                    break;
                }
            }
        }
    }
}

fn cl_block(cl_blocks: &Vec<ir::Block>, block: mir::Block) -> ir::Block {
    cl_blocks[block.0 as usize]
}

fn cl_args(args: &[mir::Reg], regs: &BTreeMap<mir::Reg, ir::Value>) -> Vec<ir::Value> {
    args.iter().map(|arg| regs[arg]).collect::<Vec<_>>()
}

fn main() {
    let source = "
fn fib(n u64) u64 {
    if n <= 1 { return 1 }
    return fib(n - 1) + fib(n - 2)
}

fn putchar(n i32)

fn main(argc u64, argv u64) u64 {
    putchar(72)
    putchar(101)
    putchar(108)
    putchar(108)
    putchar(111)
    putchar(32)
    putchar(119)
    putchar(111)
    putchar(114)
    putchar(108)
    putchar(100)
    putchar(10)

    return fib(argc)
}
";
    let mut flag_builder = cranelift_codegen::settings::builder();
    flag_builder.set("is_pic", "true").unwrap();
    let isa_builder = cranelift_codegen::isa::lookup_by_name("aarch64-apple-darwin").unwrap();
    let isa = isa_builder
        .finish(cranelift_codegen::settings::Flags::new(flag_builder))
        .unwrap();

    let mut module =
        ObjectModule::new(ObjectBuilder::new(isa, "name", default_libcall_names()).unwrap());

    let file = syntax::parse_file(source);
    let items = hir::file_items(file.clone());
    let mut analysis = hir::Analysis::default();
    let mut our_functions = Vec::new();
    let mut func_ids = HashMap::new();
    for item in items.items() {
        match item {
            &hir::ItemId::Function(func_id) => {
                let func = &items[func_id];
                let fn_syntax = func.ast.to_node(file.syntax());
                let fn_name_syntax = fn_syntax.identifier_token().unwrap();
                let fn_name = fn_name_syntax.text().to_owned();
                if fn_syntax.body().is_some() {
                    let body = hir::lower_function_body(fn_syntax);
                    let inference = hir::infer(&mut analysis, &items, func, &body);
                    let mir_func = mir::lower(&analysis, &items, &func, &body, &inference);
                    //eprintln!("{}", mir::print_function(&mir_func));
                    let mut sig = Signature::new(CallConv::AppleAarch64);
                    sig.returns.push(AbiParam::new(types::I64));
                    for ty in &mir_func.blocks[0].arg_tys {
                        sig.params.push(AbiParam::new(cl_ty(*ty)));
                    }
                    let function = module
                        .declare_function(&fn_name, Linkage::Export, &sig)
                        .unwrap();
                    our_functions.push((function, sig, mir_func));
                    func_ids.insert(fn_name, function);
                } else {
                    let body = hir::lower_function_body(fn_syntax);
                    let inference = hir::infer(&mut analysis, &items, func, &body);
                    let mir_func = mir::lower(&analysis, &items, &func, &body, &inference);
                    let mut sig = Signature::new(CallConv::AppleAarch64);
                    sig.returns.push(AbiParam::new(types::I64));
                    for ty in &mir_func.blocks[0].arg_tys {
                        sig.params.push(AbiParam::new(cl_ty(*ty)));
                    }
                    let function = module
                        .declare_function(&fn_name, Linkage::Import, &sig)
                        .unwrap();
                    func_ids.insert(fn_name, function);
                }
            }
            hir::ItemId::Record(_) => {}
            hir::ItemId::Const(_) => {}
            hir::ItemId::Enum(_) => {}
        }
    }

    for (function, sig, mir_func) in our_functions {
        let mut ctx = Context::new();
        ctx.func.signature = sig;
        let mut fn_builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_builder_ctx);
            gen_function(&mut module, mir_func, &mut builder, &func_ids);
            builder.seal_all_blocks();
            builder.finalize();
        }
        //eprintln!("{}", ctx.func.display());
        module.define_function(function, &mut ctx).unwrap();
    }
    let module_bytes = module.finish().emit().unwrap();
    std::fs::write("prog.o", module_bytes).unwrap();
}
