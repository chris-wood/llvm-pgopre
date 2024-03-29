//===- CodeGenTarget.h - Target Class Wrapper -------------------*- C++ -*-===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This file defines wrappers for the Target class and related global
// functionality.  This makes it easier to access the data and provides a single
// place that needs to check it for validity.  All of these classes throw
// exceptions on error conditions.
//
//===----------------------------------------------------------------------===//

#ifndef CODEGEN_TARGET_H
#define CODEGEN_TARGET_H

#include "CodeGenInstruction.h"
#include <iosfwd>
#include <map>

namespace llvm {

class Record;
class RecordKeeper;

/// getValueType - Return the MVT::ValueType that the specified TableGen record
/// corresponds to.
MVT::ValueType getValueType(Record *Rec);

std::ostream &operator<<(std::ostream &OS, MVT::ValueType T);
std::string getName(MVT::ValueType T);
std::string getEnumName(MVT::ValueType T);


/// CodeGenTarget - This class corresponds to the Target class in the .td files.
///
class CodeGenTarget {
  Record *TargetRec;
  std::vector<Record*> CalleeSavedRegisters;
  MVT::ValueType PointerType;

  mutable std::map<std::string, CodeGenInstruction> Instructions;
  void ReadInstructions() const;
public:
  CodeGenTarget();

  Record *getTargetRecord() const { return TargetRec; }
  const std::string &getName() const;

  const std::vector<Record*> &getCalleeSavedRegisters() const {
    return CalleeSavedRegisters;
  }

  MVT::ValueType getPointerType() const { return PointerType; }

  // getInstructionSet - Return the InstructionSet object.
  ///
  Record *getInstructionSet() const;

  /// getPHIInstruction - Return the designated PHI instruction.
  const CodeGenInstruction &getPHIInstruction() const;

  /// getInstructions - Return all of the instructions defined for this target.
  ///
  const std::map<std::string, CodeGenInstruction> &getInstructions() const {
    if (Instructions.empty()) ReadInstructions();
    return Instructions;
  }

  typedef std::map<std::string,
                   CodeGenInstruction>::const_iterator inst_iterator;
  inst_iterator inst_begin() const { return getInstructions().begin(); }
  inst_iterator inst_end() const { return Instructions.end(); }
};

} // End llvm namespace

#endif
