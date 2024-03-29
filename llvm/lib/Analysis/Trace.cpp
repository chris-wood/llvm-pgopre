//===- Trace.cpp - Implementation of Trace class --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This class represents a single trace of LLVM basic blocks.  A trace is a
// single entry, multiple exit, region of code that is often hot.  Trace-based
// optimizations treat traces almost like they are a large, strange, basic
// block: because the trace path is assumed to be hot, optimizations for the
// fall-through path are made at the expense of the non-fall-through paths.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/Trace.h"
#include "llvm/Function.h"
#include "llvm/Assembly/Writer.h"
#include <iostream>

using namespace llvm;

Function *Trace::getFunction() const {
  return getEntryBasicBlock()->getParent();
}


Module *Trace::getModule() const {
  return getFunction()->getParent();
}

/// print - Write trace to output stream.
///
void Trace::print (std::ostream &O) const {
  Function *F = getFunction ();
  O << "; Trace from function " << F->getName () << ", blocks:\n";
  for (const_iterator i = begin (), e = end (); i != e; ++i) {
    O << "; ";
    WriteAsOperand (O, *i, true, true, getModule ());
    O << "\n";
  }
  O << "; Trace parent function: \n" << *F;
}

/// dump - Debugger convenience method; writes trace to standard error
/// output stream.
///
void Trace::dump () const {
  print (std::cerr);
}
