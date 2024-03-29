//===- DataStructure.h - Build data structure graphs ------------*- C++ -*-===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// Implement the LLVM data structure analysis library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_DATA_STRUCTURE_H
#define LLVM_ANALYSIS_DATA_STRUCTURE_H

#include "llvm/Pass.h"
#include "llvm/Target/TargetData.h"
#include "Support/hash_set"

namespace llvm {

class Type;
class Instruction;
class DSGraph;
class DSNode;

// FIXME: move this stuff to a private header
namespace DataStructureAnalysis {
  /// isPointerType - Return true if this first class type is big enough to hold
  /// a pointer.
  ///
  bool isPointerType(const Type *Ty);
}


// LocalDataStructures - The analysis that computes the local data structure
// graphs for all of the functions in the program.
//
// FIXME: This should be a Function pass that can be USED by a Pass, and would
// be automatically preserved.  Until we can do that, this is a Pass.
//
class LocalDataStructures : public Pass {
  // DSInfo, one graph for each function
  hash_map<Function*, DSGraph*> DSInfo;
  DSGraph *GlobalsGraph;
public:
  ~LocalDataStructures() { releaseMemory(); }

  virtual bool run(Module &M);

  bool hasGraph(const Function &F) const {
    return DSInfo.find(const_cast<Function*>(&F)) != DSInfo.end();
  }

  /// getDSGraph - Return the data structure graph for the specified function.
  ///
  DSGraph &getDSGraph(const Function &F) const {
    hash_map<Function*, DSGraph*>::const_iterator I =
      DSInfo.find(const_cast<Function*>(&F));
    assert(I != DSInfo.end() && "Function not in module!");
    return *I->second;
  }

  DSGraph &getGlobalsGraph() const { return *GlobalsGraph; }

  /// print - Print out the analysis results...
  ///
  void print(std::ostream &O, const Module *M) const;

  /// releaseMemory - if the pass pipeline is done with this pass, we can
  /// release our memory...
  /// 
  virtual void releaseMemory();

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<TargetData>();
  }
};


/// BUDataStructures - The analysis that computes the interprocedurally closed
/// data structure graphs for all of the functions in the program.  This pass
/// only performs a "Bottom Up" propagation (hence the name).
///
class BUDataStructures : public Pass {
protected:
  // DSInfo, one graph for each function
  hash_map<Function*, DSGraph*> DSInfo;
  DSGraph *GlobalsGraph;
  hash_multimap<Instruction*, Function*> ActualCallees;
public:
  ~BUDataStructures() { releaseMemory(); }

  virtual bool run(Module &M);

  bool hasGraph(const Function &F) const {
    return DSInfo.find(const_cast<Function*>(&F)) != DSInfo.end();
  }

  /// getDSGraph - Return the data structure graph for the specified function.
  ///
  DSGraph &getDSGraph(const Function &F) const {
    hash_map<Function*, DSGraph*>::const_iterator I =
      DSInfo.find(const_cast<Function*>(&F));
    assert(I != DSInfo.end() && "Function not in module!");
    return *I->second;
  }

  DSGraph &getGlobalsGraph() const { return *GlobalsGraph; }

  /// print - Print out the analysis results...
  ///
  void print(std::ostream &O, const Module *M) const;

  /// releaseMemory - if the pass pipeline is done with this pass, we can
  /// release our memory...
  ///
  virtual void releaseMemory();

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<LocalDataStructures>();
  }

  typedef hash_multimap<Instruction*, Function*> ActualCalleesTy;
  const ActualCalleesTy &getActualCallees() const {
    return ActualCallees;
  }

private:
  void calculateGraph(DSGraph &G);

  void calculateReachableGraphs(Function *F);


  DSGraph &getOrCreateGraph(Function *F);

  unsigned calculateGraphs(Function *F, std::vector<Function*> &Stack,
                           unsigned &NextID, 
                           hash_map<Function*, unsigned> &ValMap);
};


/// TDDataStructures - Analysis that computes new data structure graphs
/// for each function using the closed graphs for the callers computed
/// by the bottom-up pass.
///
class TDDataStructures : public Pass {
  // DSInfo, one graph for each function
  hash_map<Function*, DSGraph*> DSInfo;
  hash_set<Function*> ArgsRemainIncomplete;
  DSGraph *GlobalsGraph;
public:
  ~TDDataStructures() { releaseMyMemory(); }

  virtual bool run(Module &M);

  bool hasGraph(const Function &F) const {
    return DSInfo.find(const_cast<Function*>(&F)) != DSInfo.end();
  }

  /// getDSGraph - Return the data structure graph for the specified function.
  ///
  DSGraph &getDSGraph(const Function &F) const {
    hash_map<Function*, DSGraph*>::const_iterator I =
      DSInfo.find(const_cast<Function*>(&F));
    assert(I != DSInfo.end() && "Function not in module!");
    return *I->second;
  }

  DSGraph &getGlobalsGraph() const { return *GlobalsGraph; }

  /// print - Print out the analysis results...
  ///
  void print(std::ostream &O, const Module *M) const;

  /// If the pass pipeline is done with this pass, we can release our memory...
  ///
  virtual void releaseMyMemory();

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<BUDataStructures>();
  }

private:
  void markReachableFunctionsExternallyAccessible(DSNode *N,
                                                  hash_set<DSNode*> &Visited);

  void inlineGraphIntoCallees(DSGraph &G);
  DSGraph &getOrCreateDSGraph(Function &F);
  void ComputePostOrder(Function &F, hash_set<DSGraph*> &Visited,
                        std::vector<DSGraph*> &PostOrder,
                        const BUDataStructures::ActualCalleesTy &ActualCallees);
};


/// CompleteBUDataStructures - This is the exact same as the bottom-up graphs,
/// but we use take a completed call graph and inline all indirect callees into
/// their callers graphs, making the result more useful for things like pool
/// allocation.
///
struct CompleteBUDataStructures : public BUDataStructures {
  virtual bool run(Module &M);

  bool hasGraph(const Function &F) const {
    return DSInfo.find(const_cast<Function*>(&F)) != DSInfo.end();
  }

  /// getDSGraph - Return the data structure graph for the specified function.
  ///
  DSGraph &getDSGraph(const Function &F) const {
    hash_map<Function*, DSGraph*>::const_iterator I =
      DSInfo.find(const_cast<Function*>(&F));
    assert(I != DSInfo.end() && "Function not in module!");
    return *I->second;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<BUDataStructures>();

    // FIXME: TEMPORARY (remove once finalization of indirect call sites in the
    // globals graph has been implemented in the BU pass)
    AU.addRequired<TDDataStructures>();
  }

  /// print - Print out the analysis results...
  ///
  void print(std::ostream &O, const Module *M) const;

private:
  unsigned calculateSCCGraphs(DSGraph &FG, std::vector<DSGraph*> &Stack,
                              unsigned &NextID, 
                              hash_map<DSGraph*, unsigned> &ValMap);
  DSGraph &getOrCreateGraph(Function &F);
  void processGraph(DSGraph &G);
};

} // End llvm namespace

#endif
