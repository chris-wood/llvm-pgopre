//===-- X86.h - Top-level interface for X86 representation ------*- C++ -*-===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This file contains the entry points for global functions defined in the x86
// target library, as used by the LLVM JIT.
//
//===----------------------------------------------------------------------===//

#ifndef TARGET_X86_H
#define TARGET_X86_H

#include <iosfwd>

namespace llvm {

class TargetMachine;
class FunctionPass;
class IntrinsicLowering;

/// createX86SimpleInstructionSelector - This pass converts an LLVM function
/// into a machine code representation in a very simple peep-hole fashion.  The
/// generated code sucks but the implementation is nice and simple.
///
FunctionPass *createX86SimpleInstructionSelector(TargetMachine &TM);

/// createX86PatternInstructionSelector - This pass converts an LLVM function
/// into a machine code representation using pattern matching and a machine
/// description file.
///
FunctionPass *createX86PatternInstructionSelector(TargetMachine &TM);

/// createX86SSAPeepholeOptimizerPass - Create a pass to perform SSA-based X86
/// specific peephole optimizations.
///
FunctionPass *createX86SSAPeepholeOptimizerPass();

/// createX86PeepholeOptimizer - Create a pass to perform X86 specific peephole
/// optimizations.
///
FunctionPass *createX86PeepholeOptimizerPass();

/// createX86FloatingPointKiller - This function returns a pass which
/// kills every floating point register at the end of each basic block
/// because our FloatingPointStackifier cannot handle them.
///
FunctionPass *createX86FloatingPointKillerPass();

/// createX86FloatingPointStackifierPass - This function returns a pass which
/// converts floating point register references and pseudo instructions into
/// floating point stack references and physical instructions.
///
FunctionPass *createX86FloatingPointStackifierPass();

/// createX86CodePrinterPass - Returns a pass that prints the X86
/// assembly code for a MachineFunction to the given output stream,
/// using the given target machine description.  This should work
/// regardless of whether the function is in SSA form.
///
FunctionPass *createX86CodePrinterPass(std::ostream &o,TargetMachine &tm);

/// createX86EmitCodeToMemory - Returns a pass that converts a register
/// allocated function into raw machine code in a dynamically
/// allocated chunk of memory.
///
FunctionPass *createEmitX86CodeToMemory();

// Defines symbolic names for X86 registers.  This defines a mapping from
// register name to register number.
//
} // End llvm namespace

#include "X86GenRegisterNames.inc"

// Defines symbolic names for the X86 instructions.
//
#include "X86GenInstrNames.inc"

#endif
