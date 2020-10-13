use std::collections::HashMap;

use super::super::{Function, FunctionData, Location, Instruction, BinaryOp, UnaryOp,
                   IntPredicate, Module, Value, Type, Cast};
use super::super::register_allocation::{Place, RegisterAllocation};
use super::FunctionMCodeMap;

use asm::{Assembler, OperandSize, Operand};
use asm::Reg::*;
use asm::Operand::{Reg, Imm, Mem, Label};

const AVAILABLE_REGISTERS: &[asm::Reg] = &[
    Rdi,
    Rsi,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
];

const ARGUMENT_REGISTERS: &[asm::Reg] = &[
    Rcx,
    Rdx,
    R8,
    R9,
];

fn type_to_operand_size(ty: Type, pointer: bool) -> OperandSize {
    fn type_to_size(ty: Type, pointer: bool) -> usize {
        if ty.is_pointer() {
            assert!(pointer, "Found disallowed pointer.");

            return 8;
        }

        // U1 -> U8.
        if !ty.is_normal_type() {
            return 1;
        }

        ty.size()
    }

    match type_to_size(ty, pointer) {
        1 => OperandSize::Bits8,
        2 => OperandSize::Bits16,
        4 => OperandSize::Bits32,
        8 => OperandSize::Bits64,
        _ => unreachable!(),
    }
}

trait OperandExt {
    fn is_memory(&self) -> bool;
}

impl OperandExt for Operand<'static> {
    fn is_memory(&self) -> bool {
        matches!(self, Mem(..))
    }
}

struct X86FunctionData {
    place_to_operand: HashMap<Place, Operand<'static>>,
    stackallocs:      HashMap<Location, i64>,
    regalloc:         RegisterAllocation,
    frame_size:       usize,
}

struct X86CodegenContext<'a> {
    func:     &'a FunctionData,
    x86_data: &'a X86FunctionData,
}

impl<'a> X86CodegenContext<'a> {
    fn resolver(&'a self, location: Location) -> Resolver<'a> {
        Resolver {
            location,
            context: self,
        }
    }
}

struct Resolver<'a> {
    location: Location,
    context:  &'a X86CodegenContext<'a>,
}

impl<'a> Resolver<'a> {
    fn resolve(&self, value: Value) -> Operand<'static> {
        let place = self.context.x86_data.regalloc.get(self.location, value);

        self.context.x86_data.place_to_operand[&place]
    }
}

pub struct X86Backend {
    asm:       Assembler,
    mcode_map: FunctionMCodeMap,
}

impl X86Backend {
    fn x86_function_data(func: &FunctionData) -> X86FunctionData {
        let regalloc = func.allocate_registers(AVAILABLE_REGISTERS.len());

        let mut place_to_operand = HashMap::new();

        // Stack layout after prologue:
        // ..
        // [rbp-YY] = stackalloc region #2
        // [rbp-XX] = stackalloc region #1
        // ....
        // [rbp-16] = slot #2
        // [rbp-8 ] = slot #1
        // [rbp+0 ] = RBP (pushed by function prologue)
        // [rbp+8 ] = return address
        // [rbp+16] = argument #1
        // [rbp+24] = argument #2
        // ..

        // Position arguments.
        for index in 0..regalloc.arguments.len() {
            let offset = 16 + index * 8;

            place_to_operand.insert(Place::Argument(index), 
                                    Mem(Some(Rbp), None, offset as i64));
        }

        let mut free_storage_end_offset = 0;
        let mut frame_size              = 0;

        // Position stack slots.
        for index in 0..regalloc.slots {
            let offset = -8 - (index as i64 * 8);

            place_to_operand.insert(Place::StackSlot(index),
                                    Mem(Some(Rbp), None, offset));

            free_storage_end_offset = offset;
            frame_size             += 8;
        }

        // Position registers.
        for (index, register) in AVAILABLE_REGISTERS.iter().enumerate() {
            place_to_operand.insert(Place::Register(index),
                                    Reg(*register));
        }

        // Make sure alignment is correct.
        assert!(free_storage_end_offset % 8 == 0);
        assert!(frame_size % 8 == 0);

        let mut stackallocs = HashMap::new();

        for label in func.reachable_labels() {
            let body = &func.blocks[&label];

            for (inst_id, inst) in body.iter().enumerate() {
                if let Instruction::StackAlloc { ty, size, .. } = inst {
                    let size = ty.size() * size;
                    let size = (size + 7) & !7;

                    free_storage_end_offset -= size as i64;
                    frame_size              += size;

                    stackallocs.insert(Location(label, inst_id), free_storage_end_offset);
                }
            }
        }

        // Make sure alignment is correct (again).
        assert!(free_storage_end_offset % 8 == 0);
        assert!(frame_size % 8 == 0);

        X86FunctionData {
            place_to_operand,
            stackallocs,
            regalloc,
            frame_size,
        }
    }

    fn generate_function_body(&mut self, cx: &X86CodegenContext) {
        let asm  = &mut self.asm;
        let func = cx.func;

        let labels = cx.func.reachable_labels();

        for (index, &label) in labels.iter().enumerate() {
            asm.label(&format!(".{}", label));

            let body       = &cx.func.blocks[&label];
            let next_label = labels.get(index + 1).copied();

            for (inst_id, inst) in body.iter().enumerate() {
                let location = Location(label, inst_id);
                let r        = cx.resolver(location);

                match inst {
                    Instruction::Const { dst, ty, imm } => {
                        let size = type_to_operand_size(*ty, false);

                        asm.with_size(size, |asm| {
                            let dst = r.resolve(*dst);

                            let imm = match size {
                                OperandSize::Bits8  => *imm as u8  as i8  as i64,
                                OperandSize::Bits16 => *imm as u16 as i16 as i64,
                                OperandSize::Bits32 => *imm as u32 as i32 as i64,
                                OperandSize::Bits64 => *imm as i64,
                            };

                            if imm > i32::MAX as i64 || imm < i32::MIN as i64 {
                                asm.mov(&[Reg(Rax), Imm(imm)]);
                                asm.mov(&[dst, Reg(Rax)]);
                            } else {
                                asm.mov(&[dst, Imm(imm)]);
                            }
                        });
                    }
                    Instruction::ArithmeticUnary  { dst, op, value, .. } => {
                        let ty    = func.value_type(*value);
                        let size  = type_to_operand_size(ty, false);

                        let dst   = r.resolve(*dst);
                        let value = r.resolve(*value);

                        let two_operands = dst == value;

                        asm.with_size(size, |asm| {
                            let operands = if two_operands {
                                [value]
                            } else {
                                asm.mov(&[Reg(Rax), value]);

                                [Reg(Rax)]
                            };

                            match op {
                                UnaryOp::Neg => asm.neg(&operands),
                                UnaryOp::Not => asm.not(&operands),
                            }

                            if !two_operands {
                                asm.mov(&[dst, Reg(Rax)]);
                            }
                        });
                    }
                    Instruction::ArithmeticBinary { dst, a, op, b } => {
                        enum OpType {
                            Normal,
                            Divmod,
                            Shift,
                        }

                        let ty   = func.value_type(*a);
                        let size = type_to_operand_size(ty, false);

                        let dst = r.resolve(*dst);
                        let a   = r.resolve(*a);
                        let b   = r.resolve(*b);

                        let two_operands = dst == a;

                        asm.with_size(size, |asm| {
                            let op_type = match op {
                                BinaryOp::Shr | BinaryOp::Shl | BinaryOp::Sar => {
                                    OpType::Shift
                                }
                                BinaryOp::ModU | BinaryOp::ModS | BinaryOp::DivU | 
                                BinaryOp::DivS => {
                                    OpType::Divmod
                                }
                                _ => OpType::Normal,
                            };

                            let mut result_reg = None;

                            // Select optimal instructions for performing operation.
                            let operands = match op_type {
                                OpType::Shift => {
                                    asm.mov(&[Reg(Rcx), b]);

                                    if two_operands {
                                        [a, Reg(Rcx)]
                                    } else {
                                        result_reg = Some(Rax);

                                        asm.mov(&[Reg(Rax), a]);

                                        [Reg(Rax), Reg(Rcx)]
                                    }
                                }
                                OpType::Divmod => {
                                    asm.mov(&[Reg(Rax), a]);

                                    // Whatever, these values won't be used anyway.
                                    [Reg(Rax), Reg(Rax)]
                                }
                                OpType::Normal => {
                                    if two_operands {
                                        if a.is_memory() && b.is_memory() {
                                            asm.mov(&[Reg(Rcx), b]);

                                            [a, Reg(Rcx)]
                                        } else {
                                            [a, b]
                                        }
                                    } else {
                                        result_reg = Some(Rax);

                                        asm.mov(&[Reg(Rax), a]);

                                        [Reg(Rax), b]
                                    }
                                }
                            };

                            match op {
                                BinaryOp::Add => asm.add(&operands),
                                BinaryOp::Sub => asm.sub(&operands),
                                BinaryOp::Mul => asm.imul(&operands),
                                BinaryOp::ModU => {
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[b]);

                                    result_reg = Some(Rdx);
                                }
                                BinaryOp::DivU => {
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[b]);

                                    result_reg = Some(Rax);
                                }
                                BinaryOp::ModS => {
                                    asm.cqo(&[]);
                                    asm.idiv(&[b]);

                                    result_reg = Some(Rdx);
                                }
                                BinaryOp::DivS => {
                                    asm.cqo(&[]);
                                    asm.idiv(&[b]);

                                    result_reg = Some(Rax);
                                }
                                BinaryOp::Shr => asm.shr(&operands),
                                BinaryOp::Shl => asm.shl(&operands),
                                BinaryOp::Sar => asm.sar(&operands),
                                BinaryOp::And => asm.and(&operands),
                                BinaryOp::Or  => asm.or(&operands),
                                BinaryOp::Xor => asm.xor(&operands),
                            }

                            if let Some(result_reg) = result_reg {
                                asm.mov(&[dst, Reg(result_reg)]);
                            }
                        });
                    }
                    Instruction::Load { dst, ptr } => {
                        let ty   = func.value_type(*dst);
                        let size = type_to_operand_size(ty, true);

                        let dst = r.resolve(*dst);
                        let ptr = r.resolve(*ptr);

                        let ptr = match ptr {
                            Reg(register) => Mem(Some(register), None, 0),
                            _             => {
                                asm.mov(&[Reg(Rax), ptr]);

                                Mem(Some(Rax), None, 0)
                            }
                        };

                        asm.with_size(size, |asm| {
                            if dst.is_memory() {
                                asm.mov(&[Reg(Rdx), ptr]);
                                asm.mov(&[dst, Reg(Rdx)]);
                            } else {
                                asm.mov(&[dst, ptr]);
                            }
                        });
                    }
                    Instruction::Store { ptr, value } => {
                        let ty   = func.value_type(*value);
                        let size = type_to_operand_size(ty, true);

                        let value = r.resolve(*value);
                        let ptr   = r.resolve(*ptr);

                        let ptr = match ptr {
                            Reg(register) => Mem(Some(register), None, 0),
                            _             => {
                                asm.mov(&[Reg(Rax), ptr]);

                                Mem(Some(Rax), None, 0)
                            }
                        };

                        asm.with_size(size, |asm| {
                            if value.is_memory() {
                                asm.mov(&[Reg(Rdx), value]);
                                asm.mov(&[ptr, Reg(Rdx)]);
                            } else {
                                asm.mov(&[ptr, value]);
                            }
                        });
                    }
                    Instruction::Cast { dst, cast, value, ty } => {
                        let size      = type_to_operand_size(*ty, true);
                        let orig_size = func.value_type(*value).size();

                        let dst   = r.resolve(*dst);
                        let value = r.resolve(*value);

                        asm.with_size(size, |asm| {
                            match cast {
                                Cast::Bitcast if value == dst => {
                                }
                                Cast::Truncate if value == dst => {
                                }
                                Cast::Bitcast => {
                                    if dst.is_memory() && value.is_memory() {
                                        asm.mov(&[Reg(Rax), value]);
                                        asm.mov(&[dst, Reg(Rax)]);
                                    } else {
                                        asm.mov(&[dst, value]);
                                    }
                                }
                                _ => {
                                    let operands = if dst.is_memory() {
                                        [Reg(Rax), value]
                                    } else {
                                        [dst, value]
                                    };

                                    let operands = &operands;

                                    match cast {
                                        Cast::Truncate => {
                                            asm.mov(operands);
                                        }
                                        Cast::ZeroExtend => {
                                            match orig_size {
                                                1 => asm.movzxb(operands),
                                                2 => asm.movzxw(operands),
                                                4 => {
                                                    asm.with_size(OperandSize::Bits32, |asm| {
                                                        asm.mov(operands);
                                                    });
                                                }
                                                _ => unreachable!(),
                                            }
                                        }
                                        Cast::SignExtend => {
                                            match orig_size {
                                                1 => asm.movsxb(operands),
                                                2 => asm.movsxw(operands),
                                                4 => asm.movsxd(operands),
                                                _ => unreachable!(),
                                            }
                                        }
                                        _ => unreachable!(),
                                    }

                                    if dst.is_memory() {
                                        asm.mov(&[dst, Reg(Rax)]);
                                    }
                                }
                            }
                        })
                    }
                    Instruction::StackAlloc { dst, .. } => {
                        let offset = cx.x86_data.stackallocs[&location];
                        let dst    = r.resolve(*dst);

                        let operand = if dst.is_memory() {
                            Reg(Rax)
                        } else {
                            dst
                        };
                        
                        asm.lea(&[operand, Mem(Some(Rbp), None, offset)]);

                        if dst.is_memory() {
                            asm.mov(&[dst, Reg(Rax)]);
                        }
                    }
                    Instruction::GetElementPtr { dst, source, index } => {
                        let index_size = func.value_type(*index).size();
                        let scale      = func.value_type(*source)
                            .strip_ptr()
                            .unwrap()
                            .size();

                        let dst    = r.resolve(*dst);
                        let source = r.resolve(*source);
                        let index  = r.resolve(*index);

                        let index = match index {
                            Reg(register) if index_size == 8 => {
                                register
                            }
                            _ => {
                                let operands = &[Reg(Rcx), index];

                                match index_size {
                                    1 => asm.movsxb(operands),
                                    2 => asm.movsxw(operands),
                                    4 => asm.movsxd(operands),
                                    8 => asm.mov(operands),
                                    _ => unreachable!(),
                                }

                                Rcx
                            }
                        };

                        let source = if let Reg(register) = source {
                            register
                        } else {
                            asm.mov(&[Reg(Rax), source]);

                            Rax
                        };

                        let operand = Mem(Some(source), Some((index, scale)), 0);

                        if dst.is_memory() {
                            asm.lea(&[Reg(Rdx), operand]);
                            asm.mov(&[dst, Reg(Rdx)]);
                        } else {
                            asm.lea(&[dst, operand]);
                        }
                    }
                    Instruction::Return { value } => {
                        if let Some(value) = value {
                            let ty = func.value_type(*value);

                            asm.with_size(type_to_operand_size(ty, true), |asm| {
                                asm.mov(&[Reg(Rax), r.resolve(*value)]);
                            });
                        }

                        if index + 1 != labels.len() {
                            asm.jmp(&[Label(".exit")]);
                        }
                    }
                    Instruction::Branch { target } => {
                        if Some(*target) != next_label {
                            let target = format!(".{}", target);

                            asm.jmp(&[Label(&target)]);
                        }
                    }
                    Instruction::BranchCond { value, on_true, on_false } => {
                        let on_true_s  = format!(".{}", on_true);
                        let on_false_s = format!(".{}", on_false);

                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[r.resolve(*value), Imm(0)]);
                        });

                        if Some(*on_true) == next_label {
                            asm.je(&[Label(&on_false_s)]);
                        } else if Some(*on_false) == next_label {
                            asm.jne(&[Label(&on_true_s)]);
                        } else {
                            asm.jne(&[Label(&on_true_s)]);
                            asm.jmp(&[Label(&on_false_s)]);
                        }
                    }
                    Instruction::IntCompare { dst, a, pred, b } => {
                        let ty   = func.value_type(*a);
                        let size = type_to_operand_size(ty, false);

                        let dst = r.resolve(*dst);
                        let a   = r.resolve(*a);
                        let b   = r.resolve(*b);

                        asm.with_size(size, |asm| {
                            asm.xor(&[Reg(Rcx), Reg(Rcx)]);

                            if a.is_memory() && b.is_memory() {
                                asm.mov(&[Reg(Rax), a]);
                                asm.cmp(&[Reg(Rax), b]);
                            } else {
                                asm.cmp(&[a, b]);
                            }

                            let operands = &[Reg(Rcx)];

                            match pred {
                                IntPredicate::Equal    => asm.sete(operands),
                                IntPredicate::NotEqual => asm.setne(operands),
                                IntPredicate::GtS      => asm.setg(operands),
                                IntPredicate::GteS     => asm.setge(operands),
                                IntPredicate::GtU      => asm.seta(operands),
                                IntPredicate::GteU     => asm.setae(operands),
                            }

                            asm.mov(&[dst, Reg(Rcx)]);
                        });
                    }
                    Instruction::Select { dst, cond, on_true, on_false } => {
                        let ty   = func.value_type(*on_true);
                        let size = type_to_operand_size(ty, false);

                        let dst      = r.resolve(*dst);
                        let on_false = r.resolve(*on_false);
                        let on_true  = r.resolve(*on_true);
                        let cond     = r.resolve(*cond);

                        asm.with_size(size, |asm| {
                            asm.mov(&[Reg(Rax), on_false]);
                        });

                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[cond, Imm(0)]);
                        });

                        // Here because cmovne doesn't support 8 bit size.
                        asm.cmovne(&[Reg(Rax), on_true]);

                        asm.with_size(size, |asm| {
                            asm.mov(&[dst, Reg(Rax)]);
                        });
                    }
                    Instruction::Call { .. } => {
                        panic!("Call is not supported yet.");
                    }
                }
            }
        }
    }
}

impl super::Backend for X86Backend {
    fn new(_: &Module) -> Self {
        Self {
            asm:       Assembler::new(),
            mcode_map: FunctionMCodeMap::new(),
        }
    }

    fn generate_function(&mut self, function_id: Function, function: &FunctionData) {
        let function_offset = self.asm.current_offset();
        let x86_data        = Self::x86_function_data(function);

        self.asm.label(&format!("function_{}", function_id.0));

        // Emit function epilogue. Setup stack frame.
        self.asm.push(&[Reg(Rbp)]);
        self.asm.mov(&[Reg(Rbp), Reg(Rsp)]);
        self.asm.sub(&[Reg(Rsp), Imm(x86_data.frame_size as i64)]);

        let used_registers: Vec<asm::Reg> = x86_data.regalloc.used_regs.iter()
            .map(|index| AVAILABLE_REGISTERS[*index])
            .collect();

        // Save all value registers that we will clobber.
        for reg in used_registers.iter() {
            self.asm.push(&[Reg(*reg)]);
        }

        // Move arguments to proper stack place.
        for (index, register) in ARGUMENT_REGISTERS.iter().enumerate()
            .take(x86_data.regalloc.arguments.len())
        {
            let offset = 16 + index * 8;

            self.asm.mov(&[Mem(Some(Rbp), None, offset as i64), Reg(*register)]);
        }

        let context = X86CodegenContext {
            x86_data: &x86_data,
            func:     function,
        };

        self.generate_function_body(&context);

        self.asm.label(".exit");

        // Restore all value registers that we clobbered.
        for reg in used_registers.iter().rev() {
            self.asm.pop(&[Reg(*reg)]);
        }

        // Restore previous stack state and return.
        self.asm.mov(&[Reg(Rsp), Reg(Rbp)]);
        self.asm.pop(&[Reg(Rbp)]);
        self.asm.ret(&[]);

        let function_size = self.asm.current_offset() - function_offset;

        self.mcode_map.insert(function_id, (function_offset, function_size));
    }

    fn finalize(self) -> (Vec<u8>, FunctionMCodeMap) {
        let X86Backend { asm, mcode_map } = self;

        (asm.into_bytes(), mcode_map)
    }
}
