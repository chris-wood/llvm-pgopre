//===- DataStructureOpt.cpp - Data Structure Analysis Based Optimizations -===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This pass uses DSA to a series of simple optimizations, like marking
// unwritten global variables 'constant'.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/DataStructure/DataStructure.h"
#include "llvm/Analysis/DataStructure/DSGraph.h"
#include "llvm/Module.h"
#include "llvm/Constant.h"
#include "Support/Statistic.h"
using namespace llvm;

namespace {
  Statistic<>
  NumGlobalsConstanted("ds-opt", "Number of globals marked constant");
  Statistic<>
  NumGlobalsIsolated("ds-opt", "Number of globals with references dropped");

  class DSOpt : public Pass {
    TDDataStructures *TD;
  public:
    bool run(Module &M) {
      TD = &getAnalysis<TDDataStructures>();
      bool Changed = OptimizeGlobals(M);
      return Changed;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<TDDataStructures>();      // Uses TD Datastructures
      AU.addPreserved<LocalDataStructures>();  // Preserves local...
      AU.addPreserved<TDDataStructures>();     // Preserves bu...
      AU.addPreserved<BUDataStructures>();     // Preserves td...
    }

  private:
    bool OptimizeGlobals(Module &M);
  };

  RegisterOpt<DSOpt> X("ds-opt", "DSA-based simple optimizations");
}

/// OptimizeGlobals - This method uses information taken from DSA to optimize
/// global variables.
///
bool DSOpt::OptimizeGlobals(Module &M) {
  DSGraph &GG = TD->getGlobalsGraph();
  const DSGraph::ScalarMapTy &SM = GG.getScalarMap();
  bool Changed = false;

  for (Module::giterator I = M.gbegin(), E = M.gend(); I != E; ++I)
    if (!I->isExternal()) { // Loop over all of the non-external globals...
      // Look up the node corresponding to this global, if it exists.
      DSNode *GNode = 0;
      DSGraph::ScalarMapTy::const_iterator SMI = SM.find(I);
      if (SMI != SM.end()) GNode = SMI->second.getNode();
    
      if (GNode == 0 && I->hasInternalLinkage()) {
        // If there is no entry in the scalar map for this global, it was never
        // referenced in the program.  If it has internal linkage, that means we
        // can delete it.  We don't ACTUALLY want to delete the global, just
        // remove anything that references the global: later passes will take
        // care of nuking it.
        if (!I->use_empty()) {
          I->replaceAllUsesWith(Constant::getNullValue((Type*)I->getType()));
          ++NumGlobalsIsolated;
        }
      } else if (GNode && GNode->isComplete()) {

        // If the node has not been read or written, and it is not externally
        // visible, kill any references to it so it can be DCE'd.
        if (!GNode->isModified() && !GNode->isRead() &&I->hasInternalLinkage()){
          if (!I->use_empty()) {
            I->replaceAllUsesWith(Constant::getNullValue((Type*)I->getType()));
            ++NumGlobalsIsolated;
          }
        }

        // We expect that there will almost always be a node for this global.
        // If there is, and the node doesn't have the M bit set, we can set the
        // 'constant' bit on the global.
        if (!GNode->isModified() && !I->isConstant()) {
          I->setConstant(true);
          ++NumGlobalsConstanted;
          Changed = true;
        }
      }
    }
  return Changed;
}
