#ifndef MODEL_SERIALIZEMODELPASS_H
#define MODEL_SERIALIZEMODELPASS_H

// LLVM includes
#include "llvm/Pass.h"

// Local libraries includes
#include "revng/Model/Binary.h"
#include "revng/Model/LoadModelPass.h"

class SerializeModelPass : public llvm::ModulePass {
public:
  static char ID;

public:
  SerializeModelPass() : llvm::ModulePass(ID) {}
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override final {
    AU.setPreservesAll();
    AU.addRequired<LoadModelPass>();
  }

public:
  bool runOnModule(llvm::Module &M) override final;
};

#endif // MODEL_SERIALIZEMODELPASS_H
