//===- AsmWriterEmitter.cpp - Generate an assembly writer -----------------===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This tablegen backend is emits an assembly printer for the current target.
// Note that this is currently fairly skeletal, but will grow over time.
//
//===----------------------------------------------------------------------===//

#include "AsmWriterEmitter.h"
#include "CodeGenTarget.h"
#include <ostream>
using namespace llvm;

static bool isIdentChar(char C) {
  return (C >= 'a' && C <= 'z') ||
         (C >= 'A' && C <= 'Z') ||
         (C >= '0' && C <= '9') ||
         C == '_';
}

void AsmWriterEmitter::run(std::ostream &O) {
  EmitSourceFileHeader("Assembly Writer Source Fragment", O);

  CodeGenTarget Target;
  O <<
  "/// printInstruction - This method is automatically generated by tablegen\n"
  "/// from the instruction set description.  This method returns true if the\n"
  "/// machine instruction was sufficiently described to print it, otherwise\n"
  "/// it returns false.\n"
    "bool " << Target.getName()
            << "AsmPrinter::printInstruction(const MachineInstr *MI) {\n";
  O << "  switch (MI->getOpcode()) {\n"
       "  default: return false;\n";

  std::string Namespace = Target.inst_begin()->second.Namespace;

  for (CodeGenTarget::inst_iterator I = Target.inst_begin(),
         E = Target.inst_end(); I != E; ++I)
    if (!I->second.AsmString.empty()) {
      const std::string &AsmString = I->second.AsmString;
      O << "  case " << Namespace << "::" << I->first << ": O ";

      std::string::size_type LastEmitted = 0;
      while (LastEmitted != AsmString.size()) {
        std::string::size_type DollarPos = AsmString.find('$', LastEmitted);
        if (DollarPos == std::string::npos) DollarPos = AsmString.size();

        // Emit a constant string fragment.
        if (DollarPos != LastEmitted) {
          // TODO: this should eventually handle escaping.
          O << " << \"" << std::string(AsmString.begin()+LastEmitted,
                                       AsmString.begin()+DollarPos) << "\"";
          LastEmitted = DollarPos;
        } else if (DollarPos+1 != AsmString.size() &&
                   AsmString[DollarPos+1] == '$') {
          O << " << '$'";         // "$$" -> $
        } else {
          // Get the name of the variable.
          // TODO: should eventually handle ${foo}bar as $foo
          std::string::size_type VarEnd = DollarPos+1;
          while (VarEnd < AsmString.size() && isIdentChar(AsmString[VarEnd]))
            ++VarEnd;
          std::string VarName(AsmString.begin()+DollarPos+1,
                              AsmString.begin()+VarEnd);
          if (VarName.empty())
            throw "Stray '$' in '" + I->first +
                  "' asm string, maybe you want $$?";
          unsigned OpNo = I->second.getOperandNamed(VarName);

          // If this is a two-address instruction and we are not accessing the
          // 0th operand, remove an operand.
          if (I->second.isTwoAddress && OpNo != 0) {
            if (OpNo == 1)
              throw "Should refer to operand #0 instead of #1 for two-address"
                    " instruction '" + I->first + "'!";
            --OpNo;
          }

          O << ";  printOperand(MI->getOperand(" << OpNo << "), MVT::"
            << getName(I->second.OperandList[OpNo].Ty) << "); O ";
          LastEmitted = VarEnd;
        }
      }

      O << " << '\\n'; break;\n";
    }

  O << "  }\n"
       "  return true;\n"
       "}\n";
  EmitSourceFileTail(O);
}
