#ifndef SUPPORT_METADATAOUTPUT_H
#define SUPPORT_METADATAOUTPUT_H

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// Standard includes
#include <vector>
#include <stack>
#include <utility>

// LLVM includes
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/LLVMContext.h"

// Local libraries includes
#include "revng/Support/Assert.h"

struct MetadataOutput : public llvm::yaml::IO {
  llvm::LLVMContext &C;

  std::stack<std::vector<std::pair<llvm::Metadata *,
                                   llvm::Metadata *>>> MappingStack;
  std::stack<std::vector<llvm::Metadata *>> FlowSequenceStack;

private:
  llvm::Metadata *LastResult;
  llvm::Metadata *consume() {
    assert(LastResult != nullptr);
    llvm::Metadata *Result = LastResult;
    LastResult = nullptr;
    return Result;
  }

  void produce(llvm::Metadata *MD) {
    assert(LastResult == nullptr);
    LastResult = MD;
  }

public:
  llvm::Metadata *getResult() const {
    assert(LastResult != nullptr);
    return LastResult;
  }

  MetadataOutput(llvm::LLVMContext &C) : IO(), C(C), LastResult(nullptr) {}
  bool outputting() const override { return true; }

  unsigned beginSequence() override {
    FlowSequenceStack.push({});
    return 0;
  }
  bool preflightElement(unsigned I, void *&) override {
    return true;
  }
  void postflightElement(void*) override {
    FlowSequenceStack.top().push_back(consume());
  }
  void endSequence() override {
    produce(llvm::MDTuple::get(C, FlowSequenceStack.top()));
    FlowSequenceStack.pop();
  }
  bool canElideEmptySequence() override { revng_abort("Not implemented"); }

  unsigned beginFlowSequence() override {
    FlowSequenceStack.push({});
    return 0;
  }

  void endFlowSequence() override {
    produce(llvm::MDTuple::get(C, FlowSequenceStack.top()));
    FlowSequenceStack.pop();
  }

  bool preflightFlowElement(unsigned I, void *&Context) override {
    return true;
  }

  void postflightFlowElement(void*) override {
    FlowSequenceStack.top().push_back(consume());
  }

  bool mapTag(llvm::StringRef Tag, bool Default=false) override { revng_abort("Not implemented"); }

  void beginMapping() override {
    MappingStack.push({});
  }

  void endMapping() override {
    using namespace llvm;

    std::vector<Metadata *> Result;
    for (auto [Key, Value] : MappingStack.top()) {
      Result.push_back(MDTuple::get(C, { Key, Value }));
    }

    produce(MDTuple::get(C, Result));

    MappingStack.pop();
  }

  bool preflightKey(const char *Key,
                    bool Required,
                    bool,
                    bool &UseDefault,
                    void *&SaveInfo) override {
    MappingStack.top().emplace_back(llvm::MDString::get(C, Key), nullptr);
    return true;
  }

  void postflightKey(void*) override {
    MappingStack.top().back().second = consume();
  }

  std::vector<llvm::StringRef> keys() override { revng_abort("Not implemented"); }

  void beginFlowMapping() override {}
  void endFlowMapping() override {}

  void beginEnumScalar() override {}
  bool matchEnumScalar(const char *Str, bool Match) override {
    if (Match) {
      produce(llvm::MDString::get(C, Str));
    }
    return false;
  }
  bool matchEnumFallback() override { revng_abort("Not implemented"); }
  void endEnumScalar() override {}

  bool beginBitSetScalar(bool &) override { revng_abort("Not implemented"); }
  bool bitSetMatch(const char*, bool) override { revng_abort("Not implemented"); }
  void endBitSetScalar() override {}

  void scalarString(llvm::StringRef &String,
                    llvm::yaml::QuotingType MustQuote) override {
    produce(llvm::MDString::get(C, String));
  }

  void blockScalarString(llvm::StringRef &) override {}
  void scalarTag(std::string &) override {}

  llvm::yaml::NodeKind getNodeKind() override { revng_abort("Not implemented"); }

  void setError(const llvm::Twine &) override { revng_abort("Not implemented"); }

};

template <typename T>
inline typename std::enable_if<llvm::yaml::has_MappingTraits<T, llvm::yaml::EmptyContext>::value,
                               MetadataOutput &>::type
operator<<(MetadataOutput &yout, T &map) {
  llvm::yaml::EmptyContext Ctx;
  yamlize(yout, map, true, Ctx);
  return yout;
}

#endif // SUPPORT_METADATAOUTPUT_H
