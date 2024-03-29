//===-- Interpreter.h ------------------------------------------*- C++ -*--===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This header file defines the interpreter structure
//
//===----------------------------------------------------------------------===//

#ifndef LLI_INTERPRETER_H
#define LLI_INTERPRETER_H

#include "llvm/Function.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Target/TargetData.h"
#include "Support/DataTypes.h"
#include <iostream>

namespace llvm {

struct FunctionInfo;
template<typename T> class generic_gep_type_iterator;
class ConstantExpr;
typedef generic_gep_type_iterator<User::const_op_iterator> gep_type_iterator;


// AllocaHolder - Object to track all of the blocks of memory allocated by
// alloca.  When the function returns, this object is popped off the execution
// stack, which causes the dtor to be run, which frees all the alloca'd memory.
//
class AllocaHolder {
  friend class AllocaHolderHandle;
  std::vector<void*> Allocations;
  unsigned RefCnt;
public:
  AllocaHolder() : RefCnt(0) {}
  void add(void *mem) { Allocations.push_back(mem); }
  ~AllocaHolder() {
    for (unsigned i = 0; i < Allocations.size(); ++i)
      free(Allocations[i]);
  }
};

// AllocaHolderHandle gives AllocaHolder value semantics so we can stick it into
// a vector...
//
class AllocaHolderHandle {
  AllocaHolder *H;
public:
  AllocaHolderHandle() : H(new AllocaHolder()) { H->RefCnt++; }
  AllocaHolderHandle(const AllocaHolderHandle &AH) : H(AH.H) { H->RefCnt++; }
  ~AllocaHolderHandle() { if (--H->RefCnt == 0) delete H; }

  void add(void *mem) { H->add(mem); }
};

typedef std::vector<GenericValue> ValuePlaneTy;

// ExecutionContext struct - This struct represents one stack frame currently
// executing.
//
struct ExecutionContext {
  Function             *CurFunction;// The currently executing function
  BasicBlock           *CurBB;      // The currently executing BB
  BasicBlock::iterator  CurInst;    // The next instruction to execute
  std::map<Value *, GenericValue> Values; // LLVM values used in this invocation
  std::vector<GenericValue>  VarArgs; // Values passed through an ellipsis
  CallSite             Caller;     // Holds the call that called subframes.
                                   // NULL if main func or debugger invoked fn
  AllocaHolderHandle    Allocas;    // Track memory allocated by alloca
};

// Interpreter - This class represents the entirety of the interpreter.
//
class Interpreter : public ExecutionEngine, public InstVisitor<Interpreter> {
  int ExitCode;                // The exit code to be returned by the lli util
  TargetData TD;
  IntrinsicLowering *IL;

  // The runtime stack of executing code.  The top of the stack is the current
  // function record.
  std::vector<ExecutionContext> ECStack;

  // AtExitHandlers - List of functions to call when the program exits,
  // registered with the atexit() library function.
  std::vector<Function*> AtExitHandlers;

public:
  Interpreter(Module *M, bool isLittleEndian, bool isLongPointer,
              IntrinsicLowering *IL);
  ~Interpreter();

  /// runAtExitHandlers - Run any functions registered by the program's calls to
  /// atexit(3), which we intercept and store in AtExitHandlers.
  ///
  void runAtExitHandlers();

  /// create - Create an interpreter ExecutionEngine. This can never fail.  The
  /// specified IntrinsicLowering implementation will be deleted when the
  /// Interpreter execution engine is destroyed.
  ///
  static ExecutionEngine *create(Module *M, IntrinsicLowering *IL);

  /// run - Start execution with the specified function and arguments.
  ///
  virtual GenericValue runFunction(Function *F,
                                   const std::vector<GenericValue> &ArgValues);

  /// recompileAndRelinkFunction - For the interpreter, functions are always
  /// up-to-date.
  ///
  virtual void *recompileAndRelinkFunction(Function *F) {
    return getPointerToFunction(F);
  }

  // Methods used to execute code:
  // Place a call on the stack
  void callFunction(Function *F, const std::vector<GenericValue> &ArgVals);
  void run();                // Execute instructions until nothing left to do

  // Opcode Implementations
  void visitReturnInst(ReturnInst &I);
  void visitBranchInst(BranchInst &I);
  void visitSwitchInst(SwitchInst &I);

  void visitBinaryOperator(BinaryOperator &I);
  void visitAllocationInst(AllocationInst &I);
  void visitFreeInst(FreeInst &I);
  void visitLoadInst(LoadInst &I);
  void visitStoreInst(StoreInst &I);
  void visitGetElementPtrInst(GetElementPtrInst &I);
  void visitPHINode(PHINode &PN) { assert(0 && "PHI nodes already handled!"); }
  void visitCastInst(CastInst &I);
  void visitSelectInst(SelectInst &I);


  void visitCallSite(CallSite CS);
  void visitCallInst(CallInst &I) { visitCallSite (CallSite (&I)); }
  void visitInvokeInst(InvokeInst &I) { visitCallSite (CallSite (&I)); }
  void visitUnwindInst(UnwindInst &I);

  void visitShl(ShiftInst &I);
  void visitShr(ShiftInst &I);
  void visitVANextInst(VANextInst &I);
  void visitVAArgInst(VAArgInst &I);
  void visitInstruction(Instruction &I) {
    std::cerr << I;
    assert(0 && "Instruction not interpretable yet!");
  }

  GenericValue callExternalFunction(Function *F, 
                                    const std::vector<GenericValue> &ArgVals);
  void exitCalled(GenericValue GV);

  void addAtExitHandler(Function *F) {
    AtExitHandlers.push_back(F);
  }

  GenericValue *getFirstVarArg () {
    return &(ECStack.back ().VarArgs[0]);
  }

  //FIXME: private:
public:
  GenericValue executeGEPOperation(Value *Ptr, gep_type_iterator I,
				   gep_type_iterator E, ExecutionContext &SF);

private:  // Helper functions
  // SwitchToNewBasicBlock - Start execution in a new basic block and run any
  // PHI nodes in the top of the block.  This is used for intraprocedural
  // control flow.
  // 
  void SwitchToNewBasicBlock(BasicBlock *Dest, ExecutionContext &SF);

  void *getPointerToFunction(Function *F) { return (void*)F; }

  void initializeExecutionEngine();
  void initializeExternalFunctions();
  GenericValue getConstantExprValue(ConstantExpr *CE, ExecutionContext &SF);
  GenericValue getOperandValue(Value *V, ExecutionContext &SF);
  GenericValue executeCastOperation(Value *SrcVal, const Type *Ty,
				    ExecutionContext &SF);
  void popStackAndReturnValueToCaller(const Type *RetTy, GenericValue Result);
};

} // End llvm namespace

#endif
