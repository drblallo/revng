// Standard includes
#include <vector>
#include <string>

// LLVM includes
#include "llvm/Support/WithColor.h"
#include "llvm/ADT/STLExtras.h"

// Local libraries includes
#include "revng/ADT/ZipMapIterator.h"
#include "revng/ADT/SortedVector.h"
#include "revng/ADT/MutableSet.h"
#include "revng/Support/MetaAddress.h"
#include "revng/Model/TupleTree.h"
#include "revng/Model/TupleTreeDiff.h"
#include "revng/ADT/KeyedObjectContainer.h"

// TODO: cleanup
// TODO: optional CRTP base class
// TODO: diffs should own their copy of the data
// TODO: add support std::map, std::set
// TODO: think about sorted vectors
// TODO: drop aborts

// Requirements:
//
// * Container
//   * Containers are iterable
//   * Types implicitly castable to std::string, or providing c_str
//     are not containers
// * Struct
//   * A Struct can have as fields other Structs, Containers,
//     std::string or integral types
//   * Every Struct that can end up in a Container must have a Key
//   * The Key of a Struct cannot change
// * Key
//   * Must have operator==
//   * Must have operator<
//   * Must implement KeyTraits

template<>
struct llvm::yaml::ScalarTraits<MetaAddress> {

  static void output(const MetaAddress &Value,
                     void *,
                     llvm::raw_ostream &Output) {
    Output << Value.toString();
  }

  static StringRef input(llvm::StringRef Scalar,
                         void *,
                         MetaAddress &Value) {
    Value = MetaAddress::fromString(Scalar);
    return StringRef();
  }

  static QuotingType mustQuote(StringRef) { return QuotingType::Double; }
};
LLVM_YAML_IS_FLOW_SEQUENCE_VECTOR(MetaAddress)

template<>
struct KeyTraits<MetaAddress> {
  static constexpr size_t IntsCount = 4;
  using IntsArray = std::array<KeyInt, IntsCount>;

  static MetaAddress fromInts(const IntsArray &KeyAsInts) {
    return MetaAddress(KeyAsInts[3],
                       static_cast<MetaAddressType::Values>(KeyAsInts[2]),
                       KeyAsInts[0],
                       KeyAsInts[1]);
  }

  static IntsArray toInts(const MetaAddress &MA) {
    return {
      MA.epoch(),
      MA.addressSpace(),
      static_cast<uint16_t>(MA.type()),
      MA.address()
    };
  }

  static std::string toString(const MetaAddress &Value) {
    return Value.toString();
  }

};

template<typename T>
struct KeyedObjectWithKeyMethod {
  using key_type = decltype(std::declval<T>().key());
  static key_type key(const T &Obj) {
    return Obj.key();
  }

  static T fromKey(const key_type &Key) { return { Key }; }
};

template<>
struct KeyedObjectTraits<MetaAddress>
  : public IdentityKeyedObjectTraits<MetaAddress> {};

//
// EdgeType
//
enum EdgeType {
  Invalid,
  FunctionLocal,
  Call,
  Return
};

namespace llvm::yaml {
template<>
struct ScalarEnumerationTraits<EdgeType> {
  static void enumeration(IO &io, EdgeType &V) {
    io.enumCase(V, "FunctionLocal", FunctionLocal);
    io.enumCase(V, "Call", Call);
    io.enumCase(V, "Return", Return);
  }
};
}

//
// Edge
//
struct Edge {
  MetaAddress Source;
  MetaAddress Destination;
  Edge key() const { return *this; }

  bool operator==(const Edge &) const = default;
  bool operator<(const Edge &Other) const {
    return std::tie(Source, Destination) < std::tie(Other.Source, Other.Destination);
  }
};
INTROSPECTION(Edge, Source, Destination)
LLVM_YAML_IS_SEQUENCE_VECTOR(Edge)

template<>
struct KeyedObjectTraits<Edge> : public KeyedObjectWithKeyMethod<Edge> {};

template<>
struct llvm::yaml::MappingTraits<Edge>
  : public TupleLikeMappingTraits<Edge> {};

template<>
struct KeyTraits<Edge> {
  static constexpr size_t IntsCount = 8;
  using IntsArray = std::array<KeyInt, IntsCount>;

  static Edge fromInts(const IntsArray &KeyAsInts) {
    return {
      KeyTraits<MetaAddress>::fromInts(slice<0, 4>(KeyAsInts)),
      KeyTraits<MetaAddress>::fromInts(slice<4, 4>(KeyAsInts)),
    };
  }

  static IntsArray toInts(const Edge &E) {
    auto SourceInts = KeyTraits<MetaAddress>::toInts(E.Source);
    auto DestinationInts = KeyTraits<MetaAddress>::toInts(E.Destination);
    return {
      SourceInts[0],
      SourceInts[1],
      SourceInts[2],
      SourceInts[3],
      DestinationInts[0],
      DestinationInts[1],
      DestinationInts[2],
      DestinationInts[3]
    };
  }

  static std::string toString(const Edge &Value) {
    using namespace llvm;
    return (Twine(KeyTraits<MetaAddress>::toString(Value.Source))
            + Twine("_")
            + Twine(KeyTraits<MetaAddress>::toString(Value.Destination))).str();
  }

};

//
// FunctionEdge
//
struct FunctionEdge {
  FunctionEdge() {}
  FunctionEdge(Edge TheEdge) : TheEdge(TheEdge), Type(Invalid) {}
  FunctionEdge(MetaAddress Source,
               MetaAddress Destination,
               EdgeType Type) : TheEdge({ Source, Destination }),
                                Type(Type) {}

  Edge TheEdge;
  EdgeType Type;

  Edge key() const { return TheEdge; }

  bool operator==(const FunctionEdge &Other) const = default;

};
INTROSPECTION(FunctionEdge, TheEdge, Type)
LLVM_YAML_IS_SEQUENCE_VECTOR(FunctionEdge)
template<>
struct llvm::yaml::MappingTraits<FunctionEdge>
  : public TupleLikeMappingTraits<FunctionEdge> {};
template<>
struct KeyedObjectTraits<FunctionEdge> : public KeyedObjectWithKeyMethod<FunctionEdge> {};

//
// ModelFunction
//
struct ModelFunction {
  ModelFunction() {}
  ModelFunction(MetaAddress Entry) : Entry(Entry) {}
  ModelFunction(const std::string &Name,
                const MetaAddress &Entry,
                const SortedVector<FunctionEdge> &Edges)
    : Name(Name), Entry(Entry), Edges(Edges) {}

  MetaAddress key() const { return Entry; }

  std::string Name;
  MetaAddress Entry;
  SortedVector<FunctionEdge> Edges;

  bool operator==(const ModelFunction &) const = default;

};
INTROSPECTION(ModelFunction, Name, Entry, Edges)
LLVM_YAML_IS_SEQUENCE_VECTOR(ModelFunction)
template<>
struct llvm::yaml::MappingTraits<ModelFunction>
  : public TupleLikeMappingTraits<ModelFunction> {};

template<>
struct KeyedObjectTraits<ModelFunction> : public KeyedObjectWithKeyMethod<ModelFunction> {};

//
// Model
//
struct Model {
public:
  SortedVector<MetaAddress> JumpTargets;
  SortedVector<ModelFunction> Functions;
  MutableSet<int> X;
  SortedVector<int> Y;

  bool operator==(const Model &) const = default;

public:
  Model(const SortedVector<MetaAddress> &JumpTargets,
        const SortedVector<ModelFunction> &Functions,
        const MutableSet<int> &X,
        const SortedVector<int> &Y)
    : JumpTargets(JumpTargets), Functions(Functions), X(X), Y(Y) {}

};
INTROSPECTION(Model, JumpTargets, Functions, X, Y)
template<>
struct llvm::yaml::MappingTraits<Model>
  : public TupleLikeMappingTraits<Model> {};

/////////////////////////////////

struct DumpXML : public DefaultTupleTreeVisitor {
  unsigned Indentation = 0;

  template<typename T>
  enable_if_is_integral_t<T>
  dump(T &Element) {
    llvm::outs() << Element;
  }

  void dump(std::string &Element) {
    llvm::outs() << Element;
  }

  void dump(Edge &) {
    llvm::outs() << "Edge";
  }

  void dump(EdgeType &) {
    llvm::outs() << "EdgeType";
  }

  void dump(Model &) {
    llvm::outs() << "Model";
  }

  void dump(ModelFunction &) {
    llvm::outs() << "ModelFunction";
  }

  void dump(FunctionEdge &) {
    llvm::outs() << "FunctionEdge";
  }

  void dump(MetaAddress &) {
    llvm::outs() << "MetaAddress";
  }

  template<typename T>
  enable_if_is_container_t<T>
  dump(T &) {
    llvm::outs() << "Vector";
  }

  template<typename T>
  void preVisit(T &Element) {
    llvm::outs() << std::string(Indentation * 2, ' ') << "<";
    dump(Element);
    llvm::outs() << ">\n";
    ++Indentation;
  }

  template<typename T>
  void postVisit(T &Element) {
    --Indentation;
    llvm::outs() << std::string(Indentation * 2, ' ') << "</";
    dump(Element);
    llvm::outs() << ">\n";
  }

};

static_assert(has_yaml_v<Model>);

#if 0
template <typename T>
struct llvm::yaml::SequenceTraits<MutableSet<T>,
                      typename std::enable_if<llvm::yaml::CheckIsBool<llvm::yaml::SequenceElementTraits<T>::flow>::value>::type>
  : SequenceTraitsImpl<MutableSet<T>, llvm::yaml::SequenceElementTraits<T>::flow> {};
#endif

struct LelVisitor {
  template<typename T, size_t I, typename K>
  void visitTupleElement(K &) {
  }

  template<typename T, typename K, typename KeyT>
  void visitContainerElement(KeyT, K &) {
  }
};

// Define non-member operator<< so that Output can stream out a scalar.
static_assert(llvm::yaml::has_ScalarTraits<MetaAddress>::value);

static void run() {
  auto MA = [] (uint64_t Value) {
              return MetaAddress(Value, MetaAddressType::Generic32);
            };

  // 1. Load model
  Model M = {
             { MA(0x1000), MA(0x2000), MA(0x3000) },
             {
              {
               "Asdf",
               MA(0x1000),
               { { MA(0x1000), MA(0x1004), Call }, { MA(0x2000), MA(0x2004), Return } }
              },
             },
             { 199 },
             { 33 }
  };

  M.X.insert(200);
  M.X.insert(123);

  M.Y.insert(123);
  M.Y.insert(1000);

  LelVisitor LV;
  std::vector<KeyInt> Key { 0 };
  for (KeyInt I : KeyTraits<MetaAddress>::toInts(MA(0x1000)))
    Key.push_back(I);
  callOnPathSteps(LV, Key, M);

  revng_assert(getByPath<MetaAddress>(Key, M) == &*M.JumpTargets.begin());
  revng_assert(getByPath<SortedVector<MetaAddress>>({ 0 }, M) == &M.JumpTargets);

#if 1
  DumpXML DXML;
  visit(DXML, M);
#endif

  revng_assert(tupleIndexByName<Model>("Functions") == 1);

  Model M2 = M;
  M2.JumpTargets.clear();
  M2.JumpTargets.insert(MA(0x4000));
  M2.Functions[MA(0x1000)].Name = "Lel";
  M2.Functions[MA(0x1000)].Edges.insert(FunctionEdge { MA(0x4001), MA(0x4003), Return });
  M2.Functions[MA(0x1000)].Edges.begin()->Type = FunctionLocal;
  M2.Y.insert(12300);

  TupleTreeDiff<Model> TheDiff2 = diff(M, M2);
  TheDiff2.dump();

  Model M3 = M;
  TheDiff2.apply(M3);
  revng_assert(M3 == M2);

  revng_assert(getByKey<SortedVector<ModelFunction>>(M, 1) == &M.Functions);
  revng_assert(getByKey<ModelFunction>(M.Functions, MA(0x1000)) == &M.Functions[MA(0x1000)]);

  llvm::yaml::Output YAMLOutput(llvm::outs());
  YAMLOutput << M;

  // 3. Clone
  auto NewModel = M;

  // 4. Make changes
  NewModel.Functions[MA(0x1000)].Name = "Lol";

  // 5. Compute diff: produce undo and invalidate instances
  // TODO: Diff TheDiff = NewModel.diff(M);

  YAMLOutput << NewModel;

  llvm::LLVMContext C;
  MetadataOutput CustomIO(C);
  CustomIO << NewModel;

  auto *Result = llvm::cast<llvm::MDNode>(CustomIO.getResult());

  llvm::Module MM("", C);
  MM.getOrInsertNamedMetadata("lol")->addOperand(Result);
  MM.dump();

#if 0
  const MetaAddress X;
  MetaAddress Y;
  get<0>(X);
  get<0>(Y) = 3;
  TupleLikeTraits<MetaAddress>::template fieldName<0>();
#endif
}

static_assert(std::tuple_size<Model>::value > 0);
