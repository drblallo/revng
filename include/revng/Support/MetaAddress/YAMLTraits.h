#ifndef SUPPORT_METAADDRESS_YAMLTRAITS_H
#define SUPPORT_METAADDRESS_YAMLTRAITS_H

// LLVM includes
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/Support/raw_ostream.h"

// Local libraries includes
#include "revng/Support/MetaAddress.h"

template<>
struct llvm::yaml::ScalarTraits<MetaAddress> {

  static void
  output(const MetaAddress &Value, void *, llvm::raw_ostream &Output) {
    Output << Value.toString();
  }

  static StringRef input(llvm::StringRef Scalar, void *, MetaAddress &Value) {
    Value = MetaAddress::fromString(Scalar);
    return StringRef();
  }

  static QuotingType mustQuote(StringRef) { return QuotingType::None; }
};

#endif // SUPPORT_METAADDRESS_YAMLTRAITS_H
