use crate::ir;
use ir::{Function, FunctionData, Location, Instruction, 
         BinaryOp, UnaryOp, IntPredicate, Module};
use ir::register_allocation::{Place, RegisterAllocation};
use std::collections::HashMap;
use super::FunctionMCodeMap;

use asm::Assembler;
use asm::{Reg::*, Operand, Operand::Reg, Operand::Imm, Operand::Mem, Operand::Label, OperandSize};

fn type_to_size(ty: ir::Type, pointer: bool) -> usize {
    if ty.is_pointer() {
        assert!(pointer);
        return 8;
    }

    // U1 -> U8
    if !ty.is_normal_type() {
        return 1;
    }

    ty.size()
}

fn type_to_operand_size(ty: ir::Type, pointer: bool) -> OperandSize {
    match type_to_size(ty, pointer) {
        1 => OperandSize::Bits8,
        2 => OperandSize::Bits16,
        4 => OperandSize::Bits32,
        8 => OperandSize::Bits64,
        _ => unreachable!(),
    }
}


struct FrameData {
    place_to_operand: HashMap<Place, Operand<'static>>,
    alloca_data:      HashMap<Location, i64>,
    regalloc:         RegisterAllocation,
    frame_size:       usize,
}

const AVAILABLE_REGISTERS: &[asm::Reg] = &[
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
];

pub struct X86Backend {
    asm:       Assembler,
    mcode_map: FunctionMCodeMap,
}

impl X86Backend {
    fn function_frame_data(data: &FunctionData) -> FrameData {
        let register_count = AVAILABLE_REGISTERS.len();
        let regalloc       = data.allocate_registers(register_count);

        let mut place_to_operand = HashMap::new();

        for index in 0..regalloc.arguments.len() {
            // +8 for return adddress, +8 for push rbp.
            let offset = index * 8 + 8 + 8;

            place_to_operand.insert(Place::Argument(index), 
                                    Mem(Some(Rbp), None, offset as i64));
        }

        let mut free_offset = -8;
        let mut frame_size  = 0;

        for index in 0..regalloc.slots {
            // Start at -8.
            let offset = -(index as i64 * 8) - 8;

            place_to_operand.insert(Place::StackSlot(index),
                                    Mem(Some(Rbp), None, offset));

            free_offset = offset - 8;
            frame_size += 8;
        }

        for (index, register) in AVAILABLE_REGISTERS.iter().enumerate() {
            place_to_operand.insert(Place::Register(index),
                                    Reg(*register));
        }

        assert!(free_offset % 8 == 0);

        let mut alloca_data = HashMap::new();

        for label in data.reachable_labels() {
            let body = &data.blocks[&label];

            for (inst_id, inst) in body.iter().enumerate() {
                if let Instruction::StackAlloc { ty, size, .. } = inst {
                    let size = ty.size() * size;
                    let size = (size + 7) & !7;

                    free_offset -= size as i64;
                    frame_size  += size;

                    alloca_data.insert(Location(label, inst_id), free_offset);
                }
            }
        }

        assert!(free_offset % 8 == 0);
        assert!(frame_size % 8 == 0);

        FrameData {
            place_to_operand,
            alloca_data,
            frame_size,
            regalloc,
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


    fn generate_function(&mut self, function: Function, data: &FunctionData) {
        let function_offset = self.asm.current_offset();

        let frame = Self::function_frame_data(data);
        let asm   = &mut self.asm;

        asm.label(&format!("function{}", function.0));

        asm.push(&[Reg(Rbp)]);
        asm.mov(&[Reg(Rbp), Reg(Rsp)]);
        asm.sub(&[Reg(Rsp), Imm(frame.frame_size as i64)]);

        for reg in AVAILABLE_REGISTERS.iter() {
            asm.push(&[Reg(*reg)]);
        }

        for index in 0..usize::max(frame.regalloc.arguments.len(), 4) {
            let regs = [Rcx, Rdx, R8, R9];
            let reg  = regs[index];

            asm.mov(&[Mem(Some(Rbp), None, (16 + 8 * index) as i64), Reg(reg)]);
        }

        for label in data.reachable_labels() {
            asm.label(&format!(".{}", label));

            let body = &data.blocks[&label];

            for (inst_id, inst) in body.iter().enumerate() {

                //println!("{:?} {:x}", inst, asm.current_offset());
                let location = Location(label, inst_id);

                macro_rules! resolve_value {
                    ($value: expr) => {{
                        let place = frame.regalloc.get(location, $value);

                        frame.place_to_operand[&place]
                    }}
                }

                match inst {
                    Instruction::Const { dst, ty, imm } => {
                        asm.with_size(type_to_operand_size(*ty, false), |asm| {
                            asm.mov(&[Reg(Rax), Imm(*imm as i64)]);
                            asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                        });
                    }
                    Instruction::ArithmeticUnary  { dst, op, value, .. } => {
                        let ty = data.value_type(*value);

                        asm.with_size(type_to_operand_size(ty, false), |asm| {
                            let operands = &[resolve_value!(*value)];

                            match op {
                                UnaryOp::Neg => asm.neg(operands),
                                UnaryOp::Not => asm.not(operands),
                            }
                        });
                    }
                    Instruction::IntCompare { dst, a, pred, b } => {
                        let ty = data.value_type(*a);

                        asm.with_size(type_to_operand_size(ty, false), |asm| {
                            asm.xor(&[Reg(Rcx), Reg(Rcx)]);
                            asm.mov(&[Reg(Rdx), Imm(1)]);

                            asm.mov(&[Reg(Rax), resolve_value!(*a)]);
                            asm.cmp(&[Reg(Rax), resolve_value!(*b)]);

                            let operands = &[Reg(Rcx), Reg(Rdx)];

                            asm.with_size(OperandSize::Bits64, |asm| {
                                match pred {
                                    IntPredicate::Equal    => asm.cmove(operands),
                                    IntPredicate::NotEqual => asm.cmovne(operands),
                                    IntPredicate::GtS      => asm.cmovg(operands),
                                    IntPredicate::GteS     => asm.cmovge(operands),
                                    IntPredicate::GtU      => asm.cmova(operands),
                                    IntPredicate::GteU     => asm.cmovae(operands),
                                }
                            });

                            asm.mov(&[resolve_value!(*dst), Reg(Rcx)]);
                        });
                    }
                    Instruction::Load { dst, ptr } => {
                        let ty = data.value_type(*dst);

                        asm.mov(&[Reg(Rax), resolve_value!(*ptr)]);

                        asm.with_size(type_to_operand_size(ty, true), |asm| {
                            asm.mov(&[Reg(Rax), Mem(Some(Rax), None, 0)]);
                            asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                        });
                    }
                    Instruction::Store { ptr, value } => {
                        let ty = data.value_type(*value);

                        asm.mov(&[Reg(Rax), resolve_value!(*ptr)]);

                        asm.with_size(type_to_operand_size(ty, true), |asm| {
                            asm.mov(&[Reg(Rcx), resolve_value!(*value)]);
                            asm.mov(&[Mem(Some(Rax), None, 0), Reg(Rcx)]);
                        });
                    }
                    Instruction::Branch { target } => {
                        let target = format!(".{}", target);
                        asm.jmp(&[Label(&target)]);
                    }
                    Instruction::BranchCond { value, on_true, on_false } => {
                        let on_true  = format!(".{}", on_true);
                        let on_false = format!(".{}", on_false);

                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[resolve_value!(*value), Imm(0)]);
                        });

                        asm.jne(&[Label(&on_true)]);
                        asm.jmp(&[Label(&on_false)]);
                    }
                    Instruction::StackAlloc { dst, .. } => {
                        let offset = frame.alloca_data[&location];
                        
                        asm.lea(&[Reg(Rax), Mem(Some(Rbp), None, offset)]);
                        asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                    }
                    Instruction::GetElementPtr { dst, source, index } => {
                        asm.mov(&[Reg(Rax), resolve_value!(*source)]);

                        let operands = &[Reg(Rcx), resolve_value!(*index)];

                        match data.value_type(*index).size() {
                            1 => asm.movsxb(operands),
                            2 => asm.movsxw(operands),
                            4 => asm.movsxd(operands),
                            8 => asm.mov(operands),
                            _ => unreachable!(),
                        }

                        let scale = data.value_type(*source).strip_ptr().unwrap().size();

                        asm.lea(&[Reg(Rax), Mem(Some(Rax), Some((Rcx, scale)), 0)]);
                        asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                    }
                    Instruction::Cast { dst, cast, value, ty } => {
                        match cast {
                            ir::Cast::Bitcast => {
                                asm.mov(&[Reg(Rax), resolve_value!(*value)]);
                                asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                            }
                            _ => {
                                asm.with_size(type_to_operand_size(*ty, false), |asm| {
                                    let operands  = &[Reg(Rax), resolve_value!(*value)];
                                    let orig_size = data.value_type(*value).size();

                                    match cast {
                                        ir::Cast::Truncate => {
                                            asm.mov(operands);
                                        }
                                        ir::Cast::ZeroExtend => {
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
                                        ir::Cast::SignExtend => {
                                            match orig_size {
                                                1 => asm.movsxb(operands),
                                                2 => asm.movsxw(operands),
                                                4 => asm.movsxd(operands),
                                                _ => unreachable!(),
                                            }
                                        }
                                        _ => unreachable!(),
                                    }

                                    asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                                });
                            }
                        }
                    }
                    Instruction::ArithmeticBinary { dst, a, op, b } => {
                        let ty = data.value_type(*a);

                        asm.with_size(type_to_operand_size(ty, false), |asm| {
                            asm.mov(&[Reg(Rax), resolve_value!(*a)]);
                            asm.mov(&[Reg(Rcx), resolve_value!(*b)]);

                            let operands = &[Reg(Rax), Reg(Rcx)];

                            match op {
                                BinaryOp::Add => asm.add(operands),
                                BinaryOp::Sub => asm.sub(operands),
                                BinaryOp::Mul => asm.imul(operands),
                                BinaryOp::ModU => {
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[Reg(Rcx)]);
                                    asm.mov(&[Reg(Rax), Reg(Rdx)]);
                                }
                                BinaryOp::DivU => {
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[Reg(Rcx)]);
                                }
                                BinaryOp::ModS => {
                                    asm.cqo(&[]);
                                    asm.idiv(&[Reg(Rcx)]);
                                    asm.mov(&[Reg(Rax), Reg(Rdx)]);
                                }
                                BinaryOp::DivS => {
                                    asm.cqo(&[]);
                                    asm.idiv(&[Reg(Rcx)]);
                                }
                                BinaryOp::Shr => asm.shr(operands),
                                BinaryOp::Shl => asm.shl(operands),
                                BinaryOp::Sar => asm.sar(operands),
                                BinaryOp::And => asm.and(operands),
                                BinaryOp::Or  => asm.or(operands),
                                BinaryOp::Xor => asm.xor(operands),
                            }

                            asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                        });
                    }
                    Instruction::Return { value } => {
                        if let Some(value) = value {
                            let ty = data.value_type(*value);

                            asm.with_size(type_to_operand_size(ty, true), |asm| {
                                asm.mov(&[Reg(Rax), resolve_value!(*value)]);
                            });
                        }

                        asm.jmp(&[Label(".exit")]);
                    }
                    Instruction::Select { dst, cond, on_true, on_false } => {
                        let ty = data.value_type(*on_true);

                        asm.with_size(type_to_operand_size(ty, false), |asm| {
                            asm.mov(&[Reg(Rax), resolve_value!(*on_false)]);
                        });

                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[resolve_value!(*cond), Imm(0)]);
                        });

                        // Here because cmovne doesn't support 8 bit size.
                        asm.cmovne(&[Reg(Rax), resolve_value!(*on_true)]);

                        asm.with_size(type_to_operand_size(ty, false), |asm| {
                            asm.mov(&[resolve_value!(*dst), Reg(Rax)]);
                        });
                    }
                    _ => panic!("{:?}", inst),
                }
            }
        }

        asm.label(".exit");

        for reg in AVAILABLE_REGISTERS.iter().rev() {
            asm.pop(&[Reg(*reg)]);
        }

        asm.mov(&[Reg(Rsp), Reg(Rbp)]);
        asm.pop(&[Reg(Rbp)]);
        asm.ret(&[]);


        let function_size = self.asm.current_offset() - function_offset;

        self.mcode_map.insert(function, (function_offset, function_size));
    }

    fn finalize(self) -> (Vec<u8>, FunctionMCodeMap) {
        let X86Backend { asm, mcode_map } = self;

        (asm.into_bytes(), mcode_map)
    }
}
