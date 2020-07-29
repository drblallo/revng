#ifndef MODEL_LOADMODELPASS_H
#define MODEL_LOADMODELPASS_H

// LLVM includes
#include "llvm/Pass.h"

// Local libraries includes
#include "revng/Model/Binary.h"

inline const char *ModelMetadataName = "revng.model";

class LoadModelPass : public llvm::ImmutablePass {
public:
  static char ID;

private:
  model::Binary TheBinary;
  bool Modified = false;

public:
  LoadModelPass() : llvm::ImmutablePass(ID) {}

public:
  bool doInitialization(llvm::Module &M) override final;
  bool doFinalization(llvm::Module &M) override final;

public:
  bool hasChanged() const { return Modified; }

  const model::Binary &getReadOnlyModel() { return TheBinary; }
  model::Binary &getWriteableModel() {
    Modified = true;
    return TheBinary;
  }

};

#endif // MODEL_LOADMODELPASS_H
