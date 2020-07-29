#ifndef MODEL_BINARY_H
#define MODEL_BINARY_H

// LLVM includes
#include "llvm/ADT/SmallString.h"

// Local libraries includes
#include "revng/ADT/KeyedObjectContainer.h"
#include "revng/ADT/MutableSet.h"
#include "revng/ADT/SortedVector.h"
#include "revng/Model/TupleTree.h"
#include "revng/Support/MetaAddress.h"
#include "revng/Support/MetaAddress/KeyTraits.h"
#include "revng/Support/MetaAddress/YAMLTraits.h"

// Forward declarations
namespace model {
class Function;
class Binary;
class FunctionEdge;
}

//
// FunctionEdgeType
//
namespace model::FunctionEdgeType {
enum Values {
  /// Invalid value
  Invalid,
  /// Branch due to function-local CFG (a regular branch)
  DirectBranch,
  /// A call to a fake function
  FakeFunctionCall,
  /// A return from a fake function
  FakeFunctionReturn,
  /// A function call for which the cache was able to produce a summary
  FunctionCall,
  /// A function call for which the target is unknown
  IndirectCall,
  /// A proper function return
  Return,
  /// A branch returning to the return address, but leaving the stack
  /// in an unexpected situation
  BrokenReturn,
  /// A branch representing an indirect tail call
  IndirectTailCall,
  /// A branch representing a longjmp or similar constructs
  LongJmp,
  /// A killer basic block (killer syscall or endless loop)
  Killer,
  /// The basic block ends with an unreachable instruction
  Unreachable
};
} // namespace FunctionEdgeType

namespace llvm::yaml {
template<>
struct ScalarEnumerationTraits<model::FunctionEdgeType::Values> {
  static void enumeration(IO &io, model::FunctionEdgeType::Values &V) {
    using namespace model::FunctionEdgeType;
    io.enumCase(V, "Invalid", Invalid);
    io.enumCase(V, "DirectBranch", DirectBranch);
    io.enumCase(V, "FakeFunctionCall", FakeFunctionCall);
    io.enumCase(V, "FakeFunctionReturn", FakeFunctionReturn);
    io.enumCase(V, "FunctionCall", FunctionCall);
    io.enumCase(V, "IndirectCall", IndirectCall);
    io.enumCase(V, "Return", Return);
    io.enumCase(V, "BrokenReturn", BrokenReturn);
    io.enumCase(V, "IndirectTailCall", IndirectTailCall);
    io.enumCase(V, "LongJmp", LongJmp);
    io.enumCase(V, "Killer", Killer);
    io.enumCase(V, "Unreachable", Unreachable);
  }
};
}

//
// FunctionEdge
//
class model::FunctionEdge {
public:
  MetaAddress Source;
  MetaAddress Destination;
  FunctionEdgeType::Values Type;

  bool operator<(const FunctionEdge &Other) const {
    return std::tie(Source,
                    Destination,
                    Type) < std::tie(Other.Source,
                                     Other.Destination,
                                     Other.Type);
  }
};
INTROSPECTION_NS(model, FunctionEdge, Source, Destination, Type);

template<>
struct llvm::yaml::MappingTraits<model::FunctionEdge>
  : public TupleLikeMappingTraits<model::FunctionEdge> {};

template<>
struct KeyedObjectTraits<model::FunctionEdge>
  : public IdentityKeyedObjectTraits<model::FunctionEdge> {};

//
// FunctionType
//
namespace model::FunctionType {
enum Values {
  Invalid, ///< An invalid entry
  Regular, ///< A normal function
  NoReturn, ///< A noreturn function
  Fake ///< A fake function
};
}

namespace llvm::yaml {
template<>
struct ScalarEnumerationTraits<model::FunctionType::Values> {
  static void enumeration(IO &io, model::FunctionType::Values &V) {
    using namespace model::FunctionType;
    io.enumCase(V, "Invalid", Invalid);
    io.enumCase(V, "Regular", Regular);
    io.enumCase(V, "NoReturn", NoReturn);
    io.enumCase(V, "Fake", Fake);
  }
};
}

//
// Function
//
class model::Function {
public:
  MetaAddress Entry;
  std::string Name;
  FunctionType::Values Type;
  SortedVector<FunctionEdge> CFG;

public:
  Function(const MetaAddress &Entry) : Entry(Entry) {}
};
INTROSPECTION_NS(model, Function, Entry, Name, Type, CFG)

template<>
struct llvm::yaml::MappingTraits<model::Function>
  : public TupleLikeMappingTraits<model::Function> {};

template<>
struct KeyedObjectTraits<model::Function> {
  static MetaAddress key(const model::Function &F) { return F.Entry; }
  static model::Function fromKey(const MetaAddress &Key) {
    return model::Function(Key);
  };
};

//
// Binary
//
class model::Binary {
public:
  MutableSet<Function> Functions;
};
INTROSPECTION_NS(model, Binary, Functions)

template<>
struct llvm::yaml::MappingTraits<model::Binary>
  : public TupleLikeMappingTraits<model::Binary> {};

#endif // MODEL_BINARY_H
