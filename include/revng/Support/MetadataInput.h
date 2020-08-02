#ifndef SUPPORT_METADATAINPUT_H
#define SUPPORT_METADATAINPUT_H

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// LLVM includes
#include "llvm/IR/Metadata.h"
#include "llvm/Support/YAMLTraits.h"

// Local libraries includes
#include "revng/Support/Assert.h"
#include "revng/Support/YAMLTraits.h"

struct MetadataInput : public llvm::yaml::IO {
  std::stack<llvm::Metadata *> Stack;

  template<typename T>
  T *top() {
    return llvm::cast<T>(Stack.top());
  }

  MetadataInput(llvm::Metadata *Root) : IO(), Stack() { Stack.push(Root); }
  bool outputting() const override { return false; }

  unsigned beginSequence() override { revng_abort("Not implemented"); }
  bool preflightElement(unsigned, void *&) override {
    revng_abort("Not implemented");
  }
  void postflightElement(void *) override {}
  void endSequence() override {}
  bool canElideEmptySequence() override { revng_abort("Not implemented"); }

  unsigned beginFlowSequence() override {
    return top<llvm::MDTuple>()->getNumOperands();
  }

  void endFlowSequence() override {}

  bool preflightFlowElement(unsigned I, void *&Context) override {
    Stack.push(top<llvm::MDTuple>()->getOperand(I));
    return true;
  }

  void postflightFlowElement(void *) override { Stack.pop(); }

  bool mapTag(llvm::StringRef Tag, bool Default = false) override {
    revng_abort("Not implemented");
  }

  void beginMapping() override {}

  void endMapping() override {}

  bool preflightKey(const char *Key,
                    bool Required,
                    bool,
                    bool &UseDefault,
                    void *&SaveInfo) override {
    using namespace llvm;
    auto *Tuple = top<MDTuple>();
    for (const MDOperand &Op : Tuple->operands()) {
      auto *Pair = cast<MDTuple>(Op.get());
      if (cast<MDString>(Pair->getOperand(0).get())->getString() == Key) {
        Stack.push(Pair->getOperand(1).get());
        return true;
      }
    }
    return false;
  }

  void postflightKey(void *) override { Stack.pop(); }

  std::vector<llvm::StringRef> keys() override {
    revng_abort("Not implemented");
  }

  void beginFlowMapping() override {}
  void endFlowMapping() override {}

  void beginEnumScalar() override {}
  bool matchEnumScalar(const char *Str, bool) override {
    return top<llvm::MDString>()->getString() == Str;
  }
  bool matchEnumFallback() override { revng_abort("Not implemented"); }
  void endEnumScalar() override {}

  bool beginBitSetScalar(bool &) override { revng_abort("Not implemented"); }
  bool bitSetMatch(const char *, bool) override {
    revng_abort("Not implemented");
  }
  void endBitSetScalar() override {}

  void scalarString(llvm::StringRef &String,
                    llvm::yaml::QuotingType MustQuote) override {
    String = top<llvm::MDString>()->getString();
  }

  void blockScalarString(llvm::StringRef &) override {}
  void scalarTag(std::string &) override {}

  llvm::yaml::NodeKind getNodeKind() override {
    revng_abort("Not implemented");
  }

  void setError(const llvm::Twine &) override {
    revng_abort("Not implemented");
  }
};

// Define non-member operator>> so that Input can stream in a map as a
// document.
template<typename T>
inline enable_if_has_MappingTraits<T, MetadataInput &>
operator>>(MetadataInput &yin, T &docMap) {
  llvm::yaml::EmptyContext Ctx;
  // yin.setCurrentDocument();
  yamlize(yin, docMap, true, Ctx);
  return yin;
}

#endif // SUPPORT_METADATAINPUT_H
