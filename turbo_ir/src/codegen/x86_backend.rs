use crate::{Function, FunctionData, Location, Instruction, BinaryOp, UnaryOp,
            IntPredicate, Module, Value, Type, Cast, Map};
use super::register_allocation::{Place, RegisterAllocation};
use super::FunctionMCodeMap;

use asm::{Assembler, OperandSize, Operand};
use asm::Operand::{Reg, Imm, Mem, Label};
use asm::Reg::*;

const AVAILABLE_REGISTERS: &[asm::Reg] = &[
    // Non-volatile, don't require REX.
    Rdi,
    Rsi,
    Rbx,

    // Non-volatile, require REX.
    R12,
    R13,
    R14,
    R15,

    // Volatile, require REX.
    R10,
    R11,
];

const ARGUMENT_REGISTERS: &[asm::Reg] = &[
    Rcx,
    Rdx,
    R8,
    R9,
];

#[derive(PartialEq, Eq)]
enum OpType {
    Normal,
    Divmod,
    Shift,
}

fn op_type(op: BinaryOp) -> OpType {
    match op {
        BinaryOp::Shr | BinaryOp::Shl | BinaryOp::Sar => {
            OpType::Shift
        }
        BinaryOp::ModU | BinaryOp::ModS | BinaryOp::DivU |
        BinaryOp::DivS => {
            OpType::Divmod
        }
        _ => OpType::Normal,
    }
}

fn win64_is_volatile(register: asm::Reg) -> bool {
    !matches!(register, Rbx | Rbp | Rdi | Rsi | Rsp | R12 | R13 | R14 | R15)
}

fn type_to_size(ty: Type, pointer: bool) -> usize {
    if ty.is_pointer() {
        assert!(pointer, "Found unexpected pointer.");

        return 8;
    }

    // U1 -> U8.
    if ty == Type::U1 {
        return 1;
    }

    ty.size()
}

fn type_to_operand_size(ty: Type, pointer: bool) -> OperandSize {
    match type_to_size(ty, pointer) {
        1 => OperandSize::Bits8,
        2 => OperandSize::Bits16,
        4 => OperandSize::Bits32,
        8 => OperandSize::Bits64,
        _ => unreachable!(),
    }
}

fn signextend(value: u64, size: OperandSize) -> i64 {
    match size {
        OperandSize::Bits8  => value as u8  as i8  as i64,
        OperandSize::Bits16 => value as u16 as i16 as i64,
        OperandSize::Bits32 => value as u32 as i32 as i64,
        OperandSize::Bits64 => value as i64,
    }
}

fn copy(asm: &mut Assembler, dst: Operand<'static>, src: Operand<'static>, temp: asm::Reg) {
    if dst.is_memory() && src.is_memory() {
        // Use intermediate register for memory-memory copy.
        asm.mov(&[Reg(temp), src]);
        asm.mov(&[dst, Reg(temp)]);
    } else {
        asm.mov(&[dst, src]);
    }
}

struct Registers {
    registers: Vec<asm::Reg>,
}

impl Registers {
    fn save_size(&self) -> usize {
        self.registers.len() * 8
    }

    fn save_registers(&self, asm: &mut Assembler) {
        for register in self.registers.iter() {
            asm.push(&[Reg(*register)]);
        }
    }

    fn restore_registers(&self, asm: &mut Assembler) {
        for register in self.registers.iter().rev() {
            asm.pop(&[Reg(*register)]);
        }
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
    place_to_operand:    Map<Place, Operand<'static>>,
    stackallocs:         Map<Location, i64>,
    register_allocation: RegisterAllocation,
    frame_size:          usize,
    used_registers:      Registers,
    volatile_registers:  Registers,
    noreturn:            bool,
    usage_count:         Vec<u32>,
}

struct X86CodegenContext<'a> {
    function: &'a FunctionData,
    x86_data: &'a X86FunctionData,
}

impl<'a> X86CodegenContext<'a> {
    fn resolver(&'a self, location: Location) -> Resolver<'a> {
        Resolver {
            location,
            context: self,
        }
    }

    fn usage_count(&self, value: Value) -> u32 {
        self.x86_data.usage_count[value.index()]
    }
}

struct Resolver<'a> {
    location: Location,
    context:  &'a X86CodegenContext<'a>,
}

impl<'a> Resolver<'a> {
    fn resolve(&self, value: Value) -> Operand<'static> {
        let place = self.context.x86_data.register_allocation.get(self.location, value);

        if let Place::Constant(constant) = place {
            Imm(constant as i64)
        } else {
            self.context.x86_data.place_to_operand[&place]
        }
    }
}

pub struct X86Backend {
    asm:       Assembler,
    mcode_map: FunctionMCodeMap,
}

impl X86Backend {
    fn x86_function_data(function: &FunctionData, register_allocation: RegisterAllocation,
                         labels: &[crate::Label]) -> X86FunctionData {
        let mut place_to_operand = Map::default();

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

        let dummy_location = Location::new(function.entry(), 0);

        // Create operands for arguments.
        for &argument in &function.argument_values {
            if let Place::Argument(index) = register_allocation.get(dummy_location, argument) {
                // Account for pushed RBP and return address.
                let offset = 16 + index * 8;

                place_to_operand.insert(Place::Argument(index),
                                        Mem(Some(Rbp), None, offset as i64));
            } else {
                panic!("Function argument is in invalid place.");
            }
        }

        let mut free_storage_end_offset = 0;
        let mut frame_size              = 0;

        // Create operands for stack slots.
        for index in 0..register_allocation.slots {
            // At offset 0 there is return address.
            // RBP-8 is address of first stack slot.
            let offset = -8 - (index as i64 * 8);

            place_to_operand.insert(Place::StackSlot(index),
                                    Mem(Some(Rbp), None, offset));

            free_storage_end_offset = offset;
            frame_size             += 8;
        }

        // Create operands for hardware registers.
        for (index, register) in AVAILABLE_REGISTERS.iter().enumerate() {
            place_to_operand.insert(Place::Register(index),
                                    Reg(*register));
        }

        // Get list of all used registers.
        let used_registers: Vec<asm::Reg> = register_allocation.used_registers.iter()
            .map(|index| AVAILABLE_REGISTERS[*index])
            .collect();

        // Get list of all used volatile registers.
        let volatile_registers: Vec<asm::Reg> = used_registers.iter()
            .filter_map(|register| {
                if win64_is_volatile(*register) {
                    Some(*register)
                } else {
                    None
                }
            })
            .collect();

        // Make sure that stack is properly aligned.
        assert_eq!(free_storage_end_offset % 8, 0);
        assert_eq!(frame_size % 8, 0);

        let mut stackallocs = Map::default();
        let mut noreturn    = true;
        let mut usage_count = vec![0; function.value_count()];

        // Get information about some parts of function.
        for &label in labels {
            let body = &function.blocks[&label];

            for (inst_id, instruction) in body.iter().enumerate() {
                match instruction {
                    Instruction::StackAlloc { ty, size, .. } => {
                        // Align stackalloc size to 8 bytes.
                        let size = ty.size() * size;
                        let size = (size + 7) & !7;

                        // Adjust size and end offset.
                        free_storage_end_offset -= size as i64;
                        frame_size              += size;

                        // Register offset for this stackalloc.
                        stackallocs.insert(Location::new(label, inst_id), free_storage_end_offset);
                    }
                    Instruction::Return { .. } => {
                        // This function returns. We can't do noreturn optimizations.
                        noreturn = false;
                    }
                    _ => {}
                }

                // Count how many times value is used. It's useful for pattern based
                // code generator.
                for value in instruction.read_values() {
                    usage_count[value.index()] += 1;
                }
            }
        }

        // We can't just add argument stack area size to frame size because in the prologue
        // we are saving registers.

        // Make sure alignment is correct (again).
        assert_eq!(free_storage_end_offset % 8, 0);
        assert_eq!(frame_size % 8, 0);

        X86FunctionData {
            place_to_operand,
            stackallocs,
            register_allocation,
            frame_size,
            used_registers: Registers {
                registers: used_registers,
            },
            volatile_registers: Registers {
                registers: volatile_registers,
            },
            noreturn,
            usage_count,
        }
    }

    fn gep_operand(&mut self, cx: &X86CodegenContext, r: &Resolver<'_>,
                   source:      Value,
                   index:       Value,
                   source_temp: asm::Reg,
                   index_temp:  asm::Reg) -> Operand<'static> {
        let function   = &cx.function;
        let index_size = function.value_type(index).size();

        // Scale is equal to the size of element that pointer points to.
        let scale = type_to_size(function.value_type(source)
                                    .strip_ptr().unwrap(), true);

        let source = r.resolve(source);
        let index  = r.resolve(index);

        // We will create [source+index] operand so both source and index must
        // be in registers.

        // Move source value to register if required.
        let source = if let Reg(register) = source {
            register
        } else {
            self.asm.mov(&[Reg(source_temp), source]);

            Rax
        };

        match index {
            Imm(imm) => {
                Mem(Some(source), None, imm * scale as i64)
            }
            Reg(register) if index_size == 8 => {
                Mem(Some(source), Some((register, scale)), 0)
            }
            _ => {
                // Sign extend index to 64 bit value and move it to the register.
                let operands = &[Reg(index_temp), index];

                match index_size {
                    1 => self.asm.movsxb(operands),
                    2 => self.asm.movsxw(operands),
                    4 => self.asm.movsxd(operands),
                    8 => self.asm.mov(operands),
                    _ => unreachable!(),
                }

                Mem(Some(source), Some((index_temp, scale)), 0)
            }
        }
    }

    fn generate_gep_access(&mut self, cx: &X86CodegenContext, location: Location,
                           instructions: &[Instruction]) -> usize {
        let r        = cx.resolver(location);
        let function = &cx.function;

        match instructions {
            [Instruction::GetElementPtr { dst: gep_dst,  source, index },
             Instruction::Load          { dst: load_dst, ptr }, ..]
                 if gep_dst == ptr && cx.usage_count(*gep_dst) == 1 =>
            {
                let ty       = function.value_type(*load_dst);
                let size     = type_to_operand_size(ty, true);
                let load_dst = r.resolve(*load_dst);

                let operand = self.gep_operand(cx, &r, *source, *index, Rax, Rcx);

                self.asm.with_size(size, |asm| {
                    copy(asm, load_dst, operand, Rax);
                });

                2
            }
            [Instruction::GetElementPtr { dst: gep_dst, source, index },
             Instruction::Store         { ptr, value }, ..]
                 if gep_dst == ptr && cx.usage_count(*gep_dst) == 1 =>
            {
                let ty    = function.value_type(*value);
                let size  = type_to_operand_size(ty, true);
                let value = r.resolve(*value);

                let operand = self.gep_operand(cx, &r, *source, *index, Rax, Rcx);

                self.asm.with_size(size, |asm| {
                    copy(asm, operand, value, Rax);
                });

                2
            }
            _ => 0,
        }
    }

    fn generate_complex_gep_access(&mut self, cx: &X86CodegenContext, location: Location,
                                   mut instructions: &[Instruction]) -> usize {
        let r        = cx.resolver(location);
        let function = &cx.function;

        let mut gep_info = None;
        let mut consumed = 0;

        if let Instruction::GetElementPtr { dst, source, index } = &instructions[0] {
            if cx.usage_count(*dst) != 2 {
                return 0;
            }

            instructions = &instructions[1..];
            consumed     = 1;

            gep_info = Some((*dst, *source, *index));
        }

        match instructions {
            [Instruction::Load              { dst: loaded_value, ptr: loaded_ptr },
             Instruction::ArithmeticBinary  { dst: op_dst, a, op, b },
             Instruction::Store             { ptr: stored_ptr, value: stored_value }, ..] => {
                if loaded_ptr   != stored_ptr ||
                   loaded_value != a ||
                   loaded_value == b ||
                   stored_value != op_dst
                {
                    return 0;
                }

                if cx.usage_count(*op_dst) != 1 || cx.usage_count(*loaded_value) != 1 {
                    return 0;
                }

                if op_type(*op) != OpType::Normal {
                    return 0;
                }

                let ty   = function.value_type(*loaded_value);
                let size = type_to_operand_size(ty, true);

                let mut rhs = r.resolve(*b);

                let lhs = if let Some((gep_ptr, source, index)) = gep_info {
                    if gep_ptr != *loaded_ptr {
                        return 0;
                    }

                    self.gep_operand(cx, &r, source, index, Rax, Rcx)
                } else {
                    let ptr = r.resolve(*loaded_ptr);

                    match ptr {
                        Reg(register) => {
                            Mem(Some(register), None, 0)
                        }
                        Mem(..) => {
                            self.asm.mov(&[Reg(Rax), ptr]);

                            Mem(Some(Rax), None, 0)
                        }
                        _ => unreachable!(),
                    }
                };

                if rhs.is_memory() {
                    self.asm.mov(&[Reg(Rdx), rhs]);

                    rhs = Reg(Rdx);
                }

                let operands = [lhs, rhs];

                self.asm.with_size(size, |asm| {
                    match op {
                        BinaryOp::Add => asm.add(&operands),
                        BinaryOp::Sub => asm.sub(&operands),
                        BinaryOp::Mul => asm.imul(&operands),
                        BinaryOp::And => asm.and(&operands),
                        BinaryOp::Or  => asm.or(&operands),
                        BinaryOp::Xor => asm.xor(&operands),
                        _             => panic!(),
                    }
                });

                consumed + 3
            }
            _ => 0,
        }
    }

    fn generate_from_patterns(&mut self, cx: &X86CodegenContext, location: Location,
                              instructions: &[Instruction],
                              next_label:   Option<crate::Label>) -> usize {
        if instructions.is_empty() {
            return 0;
        }

        let generated = self.generate_complex_gep_access(cx, location, instructions);
        if  generated > 0 {
            return generated;
        }

        let generated = self.generate_gep_access(cx, location, instructions);
        if  generated > 0 {
            return generated;
        }

        let function = cx.function;
        let asm      = &mut self.asm;

        let next_location = Location::new(location.label(), location.index() + 1);

        // Create operand resolver for both current location and next location.
        let resolver      = cx.resolver(location);
        let next_resolver = cx.resolver(next_location);

        // Handle some instruction patterns in a more effective way. X86ReorderPass will try
        // to create these patterns if possible.
        //
        // If from two instructions we create one, we must make sure that one which
        // we are "destroying" has apropriate number of uses.
        let generated = match instructions {
            [Instruction::IntCompare { dst, a, pred, b },
             Instruction::BranchCond { cond, on_true, on_false }, ..]
                 if dst == cond && cx.usage_count(*dst) == 1 =>
            {
                // We can merge cmp and bcond. This will allow us to use flag registers
                // directly and avoid 2 compares and conditional instructions.

                // Get textual representations of true and false labels.
                let on_true_s:  &str = &format!(".{}", on_true);
                let on_false_s: &str = &format!(".{}", on_false);

                let ty   = function.value_type(*a);
                let size = type_to_operand_size(ty, true);

                let mut pred = *pred;
                let mut a    = resolver.resolve(*a);
                let mut b    = resolver.resolve(*b);

                // Check if there is fallthrough and on what label.
                let fallthrough = match next_label {
                    Some(x) if x == *on_true  => Some(true),
                    Some(x) if x == *on_false => Some(false),
                    _                         => None,
                };

                if let Some(true) = fallthrough {
                    // Invert the condition if we are falling through to the true label.
                    // This will make us jump to the false label if condition is not met
                    // and fallthrough to true label if it is met.
                    match pred {
                        IntPredicate::Equal    => pred = IntPredicate::NotEqual,
                        IntPredicate::NotEqual => pred = IntPredicate::Equal,
                        _                      => {
                            pred = match pred {
                                IntPredicate::GtS  => IntPredicate::GteS,
                                IntPredicate::GteS => IntPredicate::GtS,
                                IntPredicate::GtU  => IntPredicate::GteU,
                                IntPredicate::GteU => IntPredicate::GtU,
                                _                  => unreachable!(),
                            };

                            std::mem::swap(&mut a, &mut b);
                        }
                    }
                }

                // Compare two operands.
                asm.with_size(size, |asm| {
                    if a.is_memory() && b.is_memory() {
                        // Use intermediate register for memory-memory comparisons.
                        asm.mov(&[Reg(Rax), a]);
                        asm.cmp(&[Reg(Rax), b]);
                    } else {
                        asm.cmp(&[a, b]);
                    }
                });

                // Get jcc destination - it's the label we don't fallthrough to.
                // If there is no fallthrough then jcc will point to true label and
                // we will have to additonally jump to the other (false) label.
                let (target_label, other_label) = fallthrough.map(|fallthrough| {
                    match fallthrough {
                        false => (on_true_s,  None),
                        true  => (on_false_s, None),
                    }
                }).unwrap_or((on_true_s, Some(on_false_s)));

                let operands = &[Label(target_label)];

                // Jump to specified label on condition met.
                match pred {
                    IntPredicate::Equal    => asm.je(operands),
                    IntPredicate::NotEqual => asm.jne(operands),
                    IntPredicate::GtS      => asm.jg(operands),
                    IntPredicate::GteS     => asm.jge(operands),
                    IntPredicate::GtU      => asm.ja(operands),
                    IntPredicate::GteU     => asm.jae(operands),
                }

                // If there was no fallthrough we must jump to other label.
                if let Some(other_label) = other_label {
                    asm.jmp(&[Label(other_label)]);
                }

                // Consumed 2 instructions.
                2
            }
            [Instruction::IntCompare { dst: cmp_dst, a, pred, b },
             Instruction::Select     { dst: sel_dst, cond, on_true, on_false }, ..]
                if cond == cmp_dst && cx.usage_count(*cmp_dst) == 1 =>
            {
                // We can merge cmp and select. This will allow us to use flag registers
                // directly and avoid 2 compares and conditional instructions.

                let cmp_ty   = function.value_type(*a);
                let cmp_size = type_to_operand_size(cmp_ty, true);

                let sel_ty   = function.value_type(*on_true);
                let sel_size = type_to_operand_size(sel_ty, true);

                // Resolve all operands with apropriate resolvers.
                let a        = resolver.resolve(*a);
                let b        = resolver.resolve(*b);
                let on_true  = next_resolver.resolve(*on_true);
                let on_false = next_resolver.resolve(*on_false);
                let dst      = next_resolver.resolve(*sel_dst);

                // RCX will contain false value by default. cmovcc will change it
                // to true value if condition is true. Do not use `dst` here, you
                // may overwrite one of inputs.
                asm.with_size(sel_size, |asm| asm.mov(&[Reg(Rcx), on_false]));

                // Compare two operands.
                asm.with_size(cmp_size, |asm| {
                    if a.is_memory() && b.is_memory() {
                        // Use intermediate register for memory-memory comparisons.
                        asm.mov(&[Reg(Rax), a]);
                        asm.cmp(&[Reg(Rax), b]);
                    } else {
                        asm.cmp(&[a, b]);
                    }
                });

                let operands = &[Reg(Rcx), on_true];

                // Set RCX to true value if condition is true.
                // This instruction uses 64 bit operand size because there
                // is no 8 bit cmovcc instruction.
                match pred {
                    IntPredicate::Equal    => asm.cmove(operands),
                    IntPredicate::NotEqual => asm.cmovne(operands),
                    IntPredicate::GtS      => asm.cmovg(operands),
                    IntPredicate::GteS     => asm.cmovge(operands),
                    IntPredicate::GtU      => asm.cmova(operands),
                    IntPredicate::GteU     => asm.cmovae(operands),
                }

                // Move selected value to destination place from intermediate register.
                asm.with_size(sel_size, |asm| asm.mov(&[dst, Reg(Rcx)]));

                // Consumed 2 instructions.
                2
            }
            _ => 0,
        };

        generated
    }

    fn generate_function_body(&mut self, cx: &X86CodegenContext, labels: &[crate::Label]) {
        time!(generate_function_body);

        let function = cx.function;

        for (index, &label) in labels.iter().enumerate() {
            // Create local label for current block. This label will be used
            // by branch/bcond instructions.
            self.asm.label(&format!(".{}", label));

            // Get the next label to check for fallthroughs.
            let next_label = labels.get(index + 1).copied();

            let body = &cx.function.blocks[&label];

            let mut inst_id                      = 0;
            let mut instructions: &[Instruction] = body;

            // Codegen instructions until nothing is left to be done.
            while !instructions.is_empty() {
                let location = Location::new(label, inst_id);
                let inst     = &instructions[0];
                let r        = cx.resolver(location);

                // Try pattern-based code generator first.
                let generated = self.generate_from_patterns(cx, location, instructions,
                                                            next_label);

                if generated > 0 {
                    // Pattern based code generator found pattern and consumed some instructions.

                    inst_id     += generated;
                    instructions = &instructions[generated..];

                    continue;
                }

                // Fallback to single-instruction code generator.
                // Calculate values for next iteration.
                inst_id      += 1;
                instructions = &instructions[1..];

                let asm = &mut self.asm;

                match inst {
                    Instruction::Phi { dst, incoming } => {
                        // All input values are mapped to the same register. Output
                        // can be in different register, we need to check that.

                        let ty    = function.value_type(*dst);
                        let size  = type_to_operand_size(ty, true);
                        let dst   = r.resolve(*dst);
                        let value = r.resolve(incoming[0].1);

                        if dst != value {
                            asm.with_size(size, |asm| {
                                if dst.is_memory() && value.is_memory() {
                                    // Use intermediate register for memory-memory mov.
                                    asm.mov(&[Reg(Rax), value]);
                                    asm.mov(&[dst, Reg(Rax)]);
                                } else {
                                    asm.mov(&[dst, value]);
                                }
                            });
                        }
                    }
                    Instruction::ArithmeticUnary  { dst, op, value, .. } => {
                        let ty    = function.value_type(*value);
                        let size  = type_to_operand_size(ty, false);

                        let dst   = r.resolve(*dst);
                        let value = r.resolve(*value);

                        let one_operand = dst == value;

                        asm.with_size(size, |asm| {
                            let operands = if one_operand {
                                // If destination is the same as operand then we can
                                // modify value in place.
                                [dst]
                            } else {
                                // Destination and operands are different.
                                // Move `value` to `dst` and modify `dst` in place.
                                if dst.is_memory() && value.is_memory() {
                                    // Use intermediate register for memory-memory moves.
                                    asm.mov(&[Reg(Rax), value]);
                                    asm.mov(&[dst, Reg(Rax)]);
                                } else {
                                    asm.mov(&[dst, value]);
                                }

                                [dst]
                            };

                            // Do the unary operation.
                            match op {
                                UnaryOp::Neg => asm.neg(&operands),
                                UnaryOp::Not => asm.not(&operands),
                            }
                        });
                    }
                    Instruction::ArithmeticBinary { dst, a, op, b } => {
                        let ty   = function.value_type(*a);
                        let size = type_to_operand_size(ty, false);

                        let dst = r.resolve(*dst);
                        let a   = r.resolve(*a);
                        let b   = r.resolve(*b);

                        let two_operands = dst == a;

                        asm.with_size(size, |asm| {
                            // Different instructions on x86 have different constraints.
                            // Get the operation type. Each different type corresponds
                            // to different constaints.
                            let op_type = op_type(*op);

                            // Intermediate register to used.
                            let mut result_reg = None;

                            // Select optimal operands for performing operation.
                            let operands = match op_type {
                                OpType::Shift => {
                                    // First operand can be everywhere, second must be
                                    // in the RCX.

                                    asm.mov(&[Reg(Rcx), b]);

                                    if two_operands {
                                        // We can modify value in place.

                                        [a, Reg(Rcx)]
                                    } else if dst.is_memory() && a.is_memory() {
                                        // We will use intermediate RAX register as a first
                                        // operand.
                                        result_reg = Some(Rax);

                                        asm.mov(&[Reg(Rax), a]);

                                        [Reg(Rax), Reg(Rcx)]
                                    } else {
                                        // dst != a and b is cached.
                                        // We can move `a` to `dst` and do the operation on
                                        // `dst` in place.
                                        asm.mov(&[dst, a]);

                                        [dst, Reg(Rcx)]
                                    }
                                }
                                OpType::Divmod => {
                                    // First operand needs to be in the RAX,
                                    // second can be anywhere. Result register
                                    // is RAX or RDX depending on operation.
                                    // It will be set later.
                                    asm.mov(&[Reg(Rax), a]);

                                    // Whatever, these values won't be used anyway.
                                    [Reg(Rax), Reg(Rax)]
                                }
                                OpType::Normal => {
                                    if two_operands && !(*op == BinaryOp::Mul && a.is_memory()) {
                                        // We can modify value in place.

                                        if a.is_memory() && b.is_memory() {
                                            // Use intermediate RCX register for a second
                                            // operand if both are in memory.
                                            asm.mov(&[Reg(Rcx), b]);

                                            [a, Reg(Rcx)]
                                        } else {
                                            [a, b]
                                        }
                                    } else if (dst.is_memory() && a.is_memory()) ||
                                              two_operands || dst == b {
                                        // We will use intermediate RAX register as a first
                                        // operand.
                                        result_reg = Some(Rax);

                                        asm.mov(&[Reg(Rax), a]);

                                        [Reg(Rax), b]
                                    } else {
                                        // dst != a != b
                                        // We can move `a` to `dst` and do the operation on
                                        // `dst` in place.

                                        asm.mov(&[dst, a]);

                                        [dst, b]
                                    }
                                }
                            };

                            // Perform the operation.
                            match op {
                                BinaryOp::Add => asm.add(&operands),
                                BinaryOp::Sub => asm.sub(&operands),
                                BinaryOp::Mul => asm.imul(&operands),
                                BinaryOp::ModU => {
                                    // Zero extend the value.
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[b]);

                                    result_reg = Some(Rdx);
                                }
                                BinaryOp::DivU => {
                                    // Zero extend the value.
                                    asm.xor(&[Reg(Rdx), Reg(Rdx)]);
                                    asm.div(&[b]);

                                    result_reg = Some(Rax);
                                }
                                BinaryOp::ModS => {
                                    // Sign extend the value.
                                    asm.cqo(&[]);
                                    asm.idiv(&[b]);

                                    result_reg = Some(Rdx);
                                }
                                BinaryOp::DivS => {
                                    // Sign extend the value.
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

                            // If we haven't modified value in place then copy it to destination
                            // from an intermediate register.
                            if let Some(result_reg) = result_reg {
                                asm.mov(&[dst, Reg(result_reg)]);
                            }
                        });
                    }
                    Instruction::Load { dst, ptr } => {
                        let ty   = function.value_type(*dst);
                        let size = type_to_operand_size(ty, true);

                        let dst = r.resolve(*dst);
                        let ptr = r.resolve(*ptr);

                        // Move pointer value out of memory if it's on the stack.
                        let ptr = match ptr {
                            Reg(register) => Mem(Some(register), None, 0),
                            _  => {
                                asm.mov(&[Reg(Rax), ptr]);
                                Mem(Some(Rax), None, 0)
                            }
                        };

                        // Perform load with correct size.
                        asm.with_size(size, |asm| {
                            if dst.is_memory() {
                                // Use intermediate register for memory-memory loads.
                                asm.mov(&[Reg(Rdx), ptr]);
                                asm.mov(&[dst, Reg(Rdx)]);
                            } else {
                                asm.mov(&[dst, ptr]);
                            }
                        });
                    }
                    Instruction::Store { ptr, value } => {
                        let ty   = function.value_type(*value);
                        let size = type_to_operand_size(ty, true);

                        let value = r.resolve(*value);
                        let ptr   = r.resolve(*ptr);

                        // Move pointer value out of memory if it's on the stack.
                        let ptr = match ptr {
                            Reg(register) => Mem(Some(register), None, 0),
                            _  => {
                                asm.mov(&[Reg(Rax), ptr]);
                                Mem(Some(Rax), None, 0)
                            }
                        };

                        // Perform store with correct size.
                        asm.with_size(size, |asm| {
                            if value.is_memory() {
                                // Use intermediate register for memory-memory stores.
                                asm.mov(&[Reg(Rdx), value]);
                                asm.mov(&[ptr, Reg(Rdx)]);
                            } else {
                                asm.mov(&[ptr, value]);
                            }
                        });
                    }
                    Instruction::Cast { dst, cast, value, ty } => {
                        let size      = type_to_operand_size(*ty, true);
                        let orig_size = function.value_type(*value).size();

                        let dst   = r.resolve(*dst);
                        let value = r.resolve(*value);

                        // Perform cast with operand size equal to destination size.
                        asm.with_size(size, |asm| {
                            match cast {
                                Cast::Bitcast if value == dst => {
                                    // NOP in x86.
                                }
                                Cast::Truncate if value == dst => {
                                    // NOP in x86.
                                }
                                Cast::Bitcast => {
                                    // Bitcasts don't modify the value and thus
                                    // they can by implemented with a single move.
                                    if dst.is_memory() && value.is_memory() {
                                        // Use intermediate register for memory-memory moves.
                                        asm.mov(&[Reg(Rax), value]);
                                        asm.mov(&[dst, Reg(Rax)]);
                                    } else {
                                        asm.mov(&[dst, value]);
                                    }
                                }
                                _ => {
                                    // mov(zs) instructions have r, r/m encoding so
                                    // if destination is in memory it will be put
                                    // to an intermediate register first.
                                    let operands = if dst.is_memory() {
                                        [Reg(Rax), value]
                                    } else {
                                        [dst, value]
                                    };

                                    let operands = &operands;

                                    match cast {
                                        Cast::Truncate => {
                                            // Because we are sure that higher parts of the
                                            // register will not be used we can just perform
                                            // move. No need for any masking.
                                            asm.mov(operands);
                                        }
                                        Cast::ZeroExtend => {
                                            // Zero extend using movzx instructions.
                                            match orig_size {
                                                1 => asm.movzxb(operands),
                                                2 => asm.movzxw(operands),
                                                4 => {
                                                    // There is no movzx for dword->qword.
                                                    // 32 bit mov zero extends by default.
                                                    asm.with_size(OperandSize::Bits32, |asm| {
                                                        asm.mov(operands);
                                                    });
                                                }
                                                _ => unreachable!(),
                                            }
                                        }
                                        Cast::SignExtend => {
                                            // Sign extend using movsx instructions.
                                            match orig_size {
                                                1 => asm.movsxb(operands),
                                                2 => asm.movsxw(operands),
                                                4 => asm.movsxd(operands),
                                                _ => unreachable!(),
                                            }
                                        }
                                        _ => unreachable!(),
                                    }

                                    // If cast required intermediate register then
                                    // copy result to an actual destination.
                                    if dst.is_memory() {
                                        asm.mov(&[dst, Reg(Rax)]);
                                    }
                                }
                            }
                        })
                    }
                    Instruction::StackAlloc { dst, .. } => {
                        // Get RBP offset for given stackalloc.
                        let offset = cx.x86_data.stackallocs[&location];
                        let dst    = r.resolve(*dst);

                        // Because we use lea then we need to use intermediate register
                        // if destination is in memory.
                        let operand = if dst.is_memory() {
                            Reg(Rax)
                        } else {
                            dst
                        };

                        // Get stackalloc buffer address on the stack.
                        asm.lea(&[operand, Mem(Some(Rbp), None, offset)]);

                        // Copy from intermediate register to actual destination if required.
                        if dst.is_memory() {
                            asm.mov(&[dst, Reg(Rax)]);
                        }
                    }
                    Instruction::GetElementPtr { dst, source, index } => {
                        let index_size = function.value_type(*index).size();

                        // Scale is equal to size of element that pointer points to.
                        let scale = type_to_size(function.value_type(*source)
                                                 .strip_ptr().unwrap(), true);

                        let dst    = r.resolve(*dst);
                        let source = r.resolve(*source);
                        let index  = r.resolve(*index);

                        // We will do lea [source+index] so both source and index must
                        // be in registers.

                        // Move source value to register if required.
                        let source = if let Reg(register) = source {
                            register
                        } else {
                            asm.mov(&[Reg(Rax), source]);

                            Rax
                        };

                        let operand = match index {
                            Imm(imm) => {
                                Mem(Some(source), None, imm * scale as i64)
                            }
                            Reg(register) if index_size == 8 => {
                                Mem(Some(source), Some((register, scale)), 0)
                            }
                            _ => {
                                // Sign extend index to 64 bit value and move it to the register.
                                let operands = &[Reg(Rcx), index];

                                match index_size {
                                    1 => asm.movsxb(operands),
                                    2 => asm.movsxw(operands),
                                    4 => asm.movsxd(operands),
                                    8 => asm.mov(operands),
                                    _ => unreachable!(),
                                }

                                Mem(Some(source), Some((Rcx, scale)), 0)
                            }
                        };

                        // Calculate element pointer using lea.
                        if dst.is_memory() {
                            // Use intermediate register if destination is in memory.
                            asm.lea(&[Reg(Rdx), operand]);
                            asm.mov(&[dst, Reg(Rdx)]);
                        } else {
                            asm.lea(&[dst, operand]);
                        }
                    }
                    Instruction::Return { value } => {
                        if let Some(value) = value {
                            let ty   = function.value_type(*value);
                            let size = type_to_operand_size(ty, true);

                            // If there is a return value then copy it to RAX, which
                            // is where all return values go.
                            asm.with_size(size, |asm| {
                                asm.mov(&[Reg(Rax), r.resolve(*value)]);
                            });
                        }

                        // Jump to the epilogue. If it's the last label then epilogue is just
                        // below us and we don't need to jump there.
                        if index + 1 != labels.len() {
                            asm.jmp(&[Label(".exit")]);
                        }
                    }
                    Instruction::Branch { target } => {
                        // Jump to target label if it's not just below us.
                        if Some(*target) != next_label {
                            // Get textual representation of target label.
                            let target = &format!(".{}", target);

                            asm.jmp(&[Label(target)]);
                        }
                    }
                    Instruction::BranchCond { cond, on_true, on_false } => {
                        // Get textual representation of true and false labels.
                        let on_true_s  = &format!(".{}", on_true);
                        let on_false_s = &format!(".{}", on_false);

                        // Check if condition is true (nonzero) or false (zero).
                        // U1 is extended to 8 bits on x86.
                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[r.resolve(*cond), Imm(0)]);
                        });

                        // Jump to correct branch accounting for possible fallthroughs.
                        if Some(*on_true) == next_label {
                            // Retain condition if true target is fallthrough.
                            asm.je(&[Label(on_false_s)]);
                        } else if Some(*on_false) == next_label {
                            // Invert condition if false target is fallthrough.
                            asm.jne(&[Label(on_true_s)]);
                        } else {
                            // No fallthrough.
                            asm.jne(&[Label(on_true_s)]);
                            asm.jmp(&[Label(on_false_s)]);
                        }
                    }
                    Instruction::IntCompare { dst, a, pred, b } => {
                        let ty   = function.value_type(*a);
                        let size = type_to_operand_size(ty, true);

                        let dst = r.resolve(*dst);
                        let a   = r.resolve(*a);
                        let b   = r.resolve(*b);

                        // Perform the comparison with correct size.
                        asm.with_size(size, |asm| {
                            // RCX will contain 0 by default. It will change to 1 by setcc
                            // if condition is true. Do not use `dst` here, you may overwrite
                            // one of inputs.
                            asm.xor(&[Reg(Rcx), Reg(Rcx)]);

                            // Compare two values.
                            if a.is_memory() && b.is_memory() {
                                // Use intermediate register for memory-memory comparison.
                                asm.mov(&[Reg(Rax), a]);
                                asm.cmp(&[Reg(Rax), b]);
                            } else {
                                asm.cmp(&[a, b]);
                            }

                            let operands = &[Reg(Rcx)];

                            // Set RCX to 1 if condition matches.
                            match pred {
                                IntPredicate::Equal    => asm.sete(operands),
                                IntPredicate::NotEqual => asm.setne(operands),
                                IntPredicate::GtS      => asm.setg(operands),
                                IntPredicate::GteS     => asm.setge(operands),
                                IntPredicate::GtU      => asm.seta(operands),
                                IntPredicate::GteU     => asm.setae(operands),
                            }

                            // Move condtion result from intermediate register
                            // to destination place.
                            asm.mov(&[dst, Reg(Rcx)]);
                        });
                    }
                    Instruction::Select { dst, cond, on_true, on_false } => {
                        let ty   = function.value_type(*on_true);
                        let size = type_to_operand_size(ty, true);

                        let dst      = r.resolve(*dst);
                        let on_false = r.resolve(*on_false);
                        let on_true  = r.resolve(*on_true);
                        let cond     = r.resolve(*cond);

                        // RAX will contain false value by default. cmovcc will change it
                        // to true value if condition is true. Do not use `dst` here, you
                        // may overwrite one of inputs.
                        asm.with_size(size, |asm| {
                            asm.mov(&[Reg(Rax), on_false]);
                        });

                        // Check if condition is true (nonzero) or false (zero). U1 are always
                        // extended to U8 so use 8 bit comparison.
                        asm.with_size(OperandSize::Bits8, |asm| {
                            asm.cmp(&[cond, Imm(0)]);
                        });

                        // Set RAX to true value if condition is true.
                        // This instruction uses 64 bit operand size because there
                        // is no 8 bit cmovcc instruction.
                        asm.cmovne(&[Reg(Rax), on_true]);

                        // Move selected value from intermediate register to destination place.
                        asm.with_size(size, |asm| {
                            asm.mov(&[dst, Reg(Rax)]);
                        });
                    }
                    Instruction::Call { dst, func: target, args } => {
                        // At this point RSP is always 16 byte aligned.
                        // Always add shadow stack space.
                        let mut arguments_stack_size = usize::max(args.len() * 8, 0x20);

                        // Make sure that we keep the stack aligned.
                        if arguments_stack_size % 16 != 0 {
                            arguments_stack_size += 8;
                        }

                        let extern_address = function.function_info
                            .as_ref()
                            .expect("Cannot codegen call without CFI.")
                            .externs
                            .get(target)
                            .cloned();

                        if extern_address.is_some() {
                            // If this is external call we must do special precautions.
                            // We need to save all volatile registers and restore them later.
                            cx.x86_data.volatile_registers.save_registers(asm);

                            // Keep the stack aligned.
                            if cx.x86_data.volatile_registers.save_size() % 16 != 0 {
                                arguments_stack_size += 8;
                            }
                        }

                        // Allocate space for arguments.
                        asm.sub(&[Reg(Rsp), Imm(arguments_stack_size as i64)]);

                        // Copy arguments to correct place.
                        for (index, arg) in args.iter().enumerate() {
                            let arg = r.resolve(*arg);

                            // Using correct size doesn't really matter here.
                            if let Some(&register) = ARGUMENT_REGISTERS.get(index) {
                                // Some of the first arguments go to the registers.
                                asm.mov(&[Reg(register), arg]);
                            } else {
                                // Later values go on the stack.

                                let offset = index * 8;
                                let stack  = Mem(Some(Rsp), None, offset as i64);

                                if arg.is_memory() {
                                    // Use intermediate register for memory-memory mov.
                                    asm.mov(&[Reg(Rax), arg]);
                                    asm.mov(&[stack, Reg(Rax)]);
                                } else {
                                    asm.mov(&[stack, arg]);
                                }
                            }
                        }

                        // Perform the call.
                        match extern_address {
                            Some(address) => {
                                asm.mov(&[Reg(Rax), Imm(address as i64)]);
                                asm.call(&[Reg(Rax)]);
                            }
                            None => {
                                asm.call(&[Label(&format!("function_{}", target.0))]);
                            }
                        }

                        // Deallocate space for arguments.
                        asm.add(&[Reg(Rsp), Imm(arguments_stack_size as i64)]);

                        if extern_address.is_some() {
                            // Restore registers after external call.
                            cx.x86_data.volatile_registers.restore_registers(asm);
                        }

                        // Copy the return value from RAX.
                        if let Some(dst) = dst {
                            let ty   = function.value_type(*dst);
                            let size = type_to_operand_size(ty, true);

                            asm.with_size(size, |asm| {
                                asm.mov(&[r.resolve(*dst), Reg(Rax)]);
                            });
                        }
                    }
                    Instruction::Alias { dst, value } => {
                        // Copy value from one register to another. This will be
                        // created by register allocator to help handling PHIs.

                        let ty   = function.value_type(*dst);
                        let size = type_to_operand_size(ty, true);

                        let dst   = r.resolve(*dst);
                        let value = r.resolve(*value);

                        if let Operand::Imm(imm) = value {
                            // Make sure that U1 (bool) has correct constant value.
                            if ty == Type::U1 {
                                assert!(imm == 0 || imm == 1, "Invalid U1 constant {}.", imm);
                            }

                            asm.with_size(size, |asm| {
                                // Properly sign-extend value as required by x86.
                                let imm = signextend(imm as u64, size);

                                if imm > i32::MAX as i64 || imm < i32::MIN as i64 {
                                    // We must use different instructions sequence
                                    // for values which don't fit in imm32.
                                    asm.mov(&[Reg(Rax), Imm(imm)]);
                                    asm.mov(&[dst, Reg(Rax)]);
                                } else if imm != 0 || dst.is_memory() {
                                    asm.mov(&[dst, Imm(imm)]);
                                } else {
                                    asm.xor(&[dst, dst]);
                                }
                            });
                        } else if dst != value {
                            asm.with_size(size, |asm| {
                                if dst.is_memory() && value.is_memory() {
                                    // Use intermediate register for memory-memory mov.
                                    asm.mov(&[Reg(Rax), value]);
                                    asm.mov(&[dst, Reg(Rax)]);
                                } else {
                                    asm.mov(&[dst, value]);
                                }
                            });
                        }
                    }
                    Instruction::Nop => {}
                }
            }
        }
    }
}

impl super::Backend for X86Backend {
    fn new(_ir: &Module) -> Self {
        Self {
            asm:       Assembler::new(),
            mcode_map: FunctionMCodeMap::default(),
        }
    }

    fn hardware_registers(&self) -> usize {
        AVAILABLE_REGISTERS.len()
    }

    fn can_inline_constant(&self, _function: &FunctionData, value: Value, constant: i64,
                           users: &[&Instruction]) -> bool {
        // Check if constant fits in imm32.
        if !(constant as i64 >= i32::MIN as i64 && constant as i64 <= i32::MAX as i64) {
            return false;
        }

        for user in users {
            // Try to determine if we can easily use constant in particular x86 instruction.
            match user {
                Instruction::ArithmeticBinary { a, op, b, .. } => {
                    let op = *op;

                    // We can easily use this constant if it's second operand of
                    // most of arithmetic operations.
                    if *a == value || *b != value {
                        return false;
                    }

                    if op == BinaryOp::Mul || op == BinaryOp::DivU || op == BinaryOp::DivS {
                        return false;
                    }
                }
                Instruction::IntCompare { .. } => {
                    // x86 backend can change the order and therafore we cannot
                    // easily determine if constant can be used as imm.
                    // TODO: Handle this somehow.

                    /*
                    if *a == value || *b != value {
                        continue 'skip;
                    }
                    */

                    return false;
                }
                Instruction::GetElementPtr { index, .. } => {
                    if *index != value {
                        return false;
                    }
                }
                Instruction::Return { .. } => {},
                _ => return false,
            }
        }

        true
    }

    fn generate_function(&mut self, function_id: Function, function: &FunctionData,
                         register_allocation: RegisterAllocation) {
        time!(generate_function);

        let function_offset = self.asm.current_offset();
        let labels          = function.reachable_labels_dfs();
        let x86_data        = Self::x86_function_data(function, register_allocation, &labels);

        let context = X86CodegenContext {
            x86_data: &x86_data,
            function,
        };

        let mut frame_size = x86_data.frame_size;

        // Calculate expected total frame size to align it later.
        // Frame size + size of pushed registers (if function returns) + size of RBP.
        let mut expected_frame_size = frame_size + 8;

        // If function returns we need to save registers and restore them later. Adjust
        // expected frame size.
        if !context.x86_data.noreturn {
            expected_frame_size += context.x86_data.used_registers.save_size();
        }

        assert_eq!(expected_frame_size % 8, 0, "Frame size is not even 8 byte aligned.");

        // Before call stack is 16-byte aligned so after call it's not. Align the stack
        // to 16 byte boundary.
        if expected_frame_size % 16 == 0 {
            frame_size += 8;
        }

        self.asm.label(&format!("function_{}", function_id.0));

        // Emit function epilogue. Setup stack frame.
        self.asm.push(&[Reg(Rbp)]);
        self.asm.mov(&[Reg(Rbp), Reg(Rsp)]);

        // Allocate all space required on the stack.
        if frame_size > 0 {
            self.asm.sub(&[Reg(Rsp), Imm(frame_size as i64)]);
        }

        if !context.x86_data.noreturn {
            // If function returns then save all registers that we will clobber.
            context.x86_data.used_registers.save_registers(&mut self.asm);
        }

        // Move first arguments from registers to proper stack place.
        for (index, register) in ARGUMENT_REGISTERS.iter().enumerate()
            .take(function.argument_values.len())
        {
            // Account for pushed RBP and return address when calculating argument offset.
            let offset = 16 + index * 8;

            // Write argument to shadow stack space.
            // Using correct size doesn't really matter here.
            self.asm.mov(&[Mem(Some(Rbp), None, offset as i64), Reg(*register)]);
        }

        // Codegen function.
        self.generate_function_body(&context, &labels);

        if !context.x86_data.noreturn {
            // Function returns so we need to generate epilogue.

            self.asm.label(".exit");

            // Restore all value registers that we have clobbered.
            context.x86_data.used_registers.restore_registers(&mut self.asm);

            // Restore previous stack state and return.
            self.asm.mov(&[Reg(Rsp), Reg(Rbp)]);
            self.asm.pop(&[Reg(Rbp)]);
            self.asm.ret(&[]);
        }

        let function_size = self.asm.current_offset() - function_offset;

        // Add information about generated code to machine code map.
        self.mcode_map.insert(function_id, (function_offset, function_size));
    }

    fn finalize(&mut self) -> (Vec<u8>, FunctionMCodeMap) {
        let asm       = std::mem::take(&mut self.asm);
        let mcode_map = std::mem::take(&mut self.mcode_map);

        (asm.into_bytes(), mcode_map)
    }
}
