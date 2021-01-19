#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <stack>
#include <vector>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/YAMLTraits.h"

#include "revng/Support/MetadataOutput.h"
#include "revng/Support/MetadataInput.h"
#include "Model.h"

using namespace llvm;
using namespace llvm::yaml;

enum FunctionInfoType {
  Lel = 1,
  Lol = 10,
  Lul = 5
};

template <>
struct ScalarEnumerationTraits<FunctionInfoType> {
  static void enumeration(IO &io, FunctionInfoType &value) {
    io.enumCase(value, "Lel", Lel);
    io.enumCase(value, "Lol", Lol);
    io.enumCase(value, "Lul", Lul);
  }
};

struct FunctionInfo {
  FunctionInfoType Type;
  std::vector<uint64_t> BasicBlocks;
};

template <>
struct MappingTraits<FunctionInfo> {
  static void mapping(IO &io, FunctionInfo &Obj) {
    io.mapRequired("BasicBlocks",  Obj.BasicBlocks);
    io.mapRequired("Type",  Obj.Type);
  }
};

int main() {
#if 0
  constexpr size_t Size = 1024 * 1024;
  char Buffer[Size];
  fread(&Buffer, 1, Size, stdin);
#else
  char Buffer[] = "BasicBlocks: [1,2,3]\nType: Lel";
#endif

  Input YAMLInput(Buffer);
  FunctionInfo TheFunctionInfo;

  YAMLInput >> TheFunctionInfo;

  for (uint64_t N : TheFunctionInfo.BasicBlocks) {
    std::cout << N << "\n";
  }

  Output YAMLOutput(llvm::outs());
  YAMLOutput << TheFunctionInfo;

  LLVMContext C;
  MetadataOutput CustomIO(C);
  CustomIO << TheFunctionInfo;

  auto *Result = cast<MDNode>(CustomIO.getResult());

  Module M("", C);
  M.getOrInsertNamedMetadata("lol")->addOperand(Result);
  M.dump();

  TheFunctionInfo = FunctionInfo();
  MetadataInput CustomInput(Result);
  CustomInput >> TheFunctionInfo;

  for (uint64_t N : TheFunctionInfo.BasicBlocks) {
    std::cout << N << "\n";
  }

  run();

  return 0;
}
