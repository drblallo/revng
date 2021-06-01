#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <cstring>
#include <initializer_list>
#include <iterator>
#include <optional>
#include <utility>
#include <vector>

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include "revng/ADT/Hierarchy.h"
#include "revng/Support/Assert.h"
#include "revng/Support/Debug.h"

namespace AutoEnforcer {
struct Granularity : public HierarchyNode<Granularity> {
public:
  Granularity(llvm::StringRef Name) : HierarchyNode(Name) {}
  Granularity(llvm::StringRef Name, Granularity &Parent) :
    HierarchyNode<Granularity>(Name, Parent) {}
};

struct Kind : public HierarchyNode<Kind> {
public:
  Kind(llvm::StringRef Name, Granularity *Granularity) :
    HierarchyNode<Kind>(Name), Granularity(Granularity) {
    revng_assert(Granularity != nullptr);
  }
  Kind(llvm::StringRef Name, Kind &Parent, Granularity *Granularity) :
    HierarchyNode<Kind>(Name, Parent), Granularity(Granularity) {
    revng_assert(Granularity != nullptr);
  }

  Granularity *Granularity;
};

enum class KindExactness { Exact, DerivedFrom };

class AutoEnforcerQuantifier {
public:
  AutoEnforcerQuantifier(std::optional<std::string> Name) :
    Name(std::move(Name)) {}

  AutoEnforcerQuantifier() : Name(std::nullopt) {}

  bool isAll() const { return not Name.has_value(); }
  bool isSingle() const { return Name.has_value(); }

  const std::string &getName() const {
    revng_assert(isSingle());
    return *Name;
  }

  bool operator<(const AutoEnforcerQuantifier &Other) const {
    return Name < Other.Name;
  }

  template<typename OStream>
  void dump(OStream &OS) const debug_function {
    if (Name.has_value())
      OS << *Name;
    else
      OS << "*";
  }

  void dump() const debug_function { dump(dbg); }

  bool operator<=>(const AutoEnforcerQuantifier &Other) const {
    if (not Name.has_value() and not Other.Name.has_value())
      return 0;
    if (not Name.has_value())
      return -1;
    if (not Other.Name.has_value())
      return 1;
    return strcmp(Name->c_str(), Other.Name->c_str());
  }

private:
  std::optional<std::string> Name;
};

class AutoEnforcerTarget {
public:
  AutoEnforcerTarget(llvm::SmallVector<AutoEnforcerQuantifier, 3> Quantifiers,
                     const Kind &K,
                     KindExactness Exactness = KindExactness::Exact) :
    Entries(std::move(Quantifiers)), K(&K), Exact(Exactness) {}

  AutoEnforcerTarget(AutoEnforcerQuantifier Quantifier,
                     const Kind &K,
                     KindExactness Exactness = KindExactness::Exact) :
    Entries({ std::move(Quantifier) }), K(&K), Exact(Exactness) {}

  AutoEnforcerTarget(std::string Name,
                     const Kind &K,
                     KindExactness Exactness = KindExactness::Exact) :
    Entries({ AutoEnforcerQuantifier(std::move(Name)) }),
    K(&K),
    Exact(Exactness) {}

  AutoEnforcerTarget(std::initializer_list<std::string> Names,
                     const Kind &K,
                     KindExactness Exactness = KindExactness::Exact) :
    K(&K), Exact(Exactness) {
    for (auto Name : Names)
      Entries.emplace_back(std::move(Name));
  }

  AutoEnforcerTarget(llvm::ArrayRef<llvm::StringRef> Names,
                     const Kind &K,
                     KindExactness Exactness = KindExactness::Exact) :
    K(&K), Exact(Exactness) {
    for (auto Name : Names)
      Entries.emplace_back(Name.str());
  }

  bool operator<(const AutoEnforcerTarget &Other) const {
    auto Self = std::tie(Entries, K, Exact);
    auto OtherSelf = std::tie(Other.Entries, Other.K, Other.Exact);
    return Self < OtherSelf;
  }

  const Kind &getKind() const { return *K; }

  KindExactness kindExactness() const { return Exact; }
  void setKind(const Kind &NewKind) { K = &NewKind; }
  void setKindExactness(KindExactness NewExactness) { Exact = NewExactness; }

  const llvm::SmallVector<AutoEnforcerQuantifier, 3> &getQuantifiers() const {
    return Entries;
  }

  void addGranularity() { Entries.emplace_back(); }
  void dropGranularity() { Entries.pop_back(); }

  template<typename OStream>
  void dump(OStream &OS, size_t Indents = 0) const debug_function {
    indent(OS, Indents);

    OS << (Exact == KindExactness::DerivedFrom ? "derived from " : "exactly ")
       << K->getName().str() << " With path: ";
    for (const auto &Entry : Entries) {
      Entry.dump(OS);
      OS << "/";
    }
    OS << "\n";
  }

  template<typename OStream, typename Range>
  static void dumpQuantifiers(OStream &OS, Range R) debug_function {
    for (const auto &Entry : R) {
      Entry.dump(OS);
      OS << "/";
    }
  }

  void dump() const debug_function { dump(dbg); }

  int operator<=>(const AutoEnforcerTarget &Other) const;

  bool operator==(const AutoEnforcerTarget &Other) const {
    return (*this <=> Other) == 0;
  }

private:
  llvm::SmallVector<AutoEnforcerQuantifier, 3> Entries;
  const Kind *K;
  KindExactness Exact;
};

template<typename KindDictionary>
llvm::Expected<AutoEnforcerTarget>
parseAutoEnforcerTarget(llvm::StringRef AsString, const KindDictionary &Dict) {
  llvm::SmallVector<llvm::StringRef, 2> Parts;
  AsString.split(Parts, ':', 2);

  if (Parts.size() != 2)
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "string %s was not in expected form "
                                   "<path:kind>",
                                   AsString.str().c_str());

  llvm::SmallVector<llvm::StringRef, 3> Path;
  Parts[0].split(Path, '/');

  auto It = Dict.find(Parts[1]);
  if (It == Dict.end())
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "No known Kind %s in dictionary",
                                   Parts[0].str().c_str());

  return AutoEnforcerTarget(std::move(Path), *It->second);
}

class BackingContainersStatus {
public:
  using TargetContainer = llvm::SmallVector<AutoEnforcerTarget, 3>;
  using Container = llvm::StringMap<TargetContainer>;
  using iterator = Container::iterator;
  using const_iterator = Container::const_iterator;

  TargetContainer &operator[](llvm::StringRef ContainerName) {
    return ContainersStatus[ContainerName];
  }

  TargetContainer &at(llvm::StringRef ContainerName) {
    return ContainersStatus.find(ContainerName)->getValue();
  }

  const TargetContainer &at(llvm::StringRef ContainerName) const {
    return ContainersStatus.find(ContainerName)->getValue();
  }

  iterator begin() { return ContainersStatus.begin(); }
  iterator end() { return ContainersStatus.end(); }
  const_iterator begin() const { return ContainersStatus.begin(); }
  const_iterator end() const { return ContainersStatus.end(); }

  bool empty() const { return size() == 0; }
  size_t size() const {
    size_t Size = 0;
    for (const auto &Container : ContainersStatus)
      Size += Container.second.size();
    return Size;
  }

  void add(llvm::StringRef Name,
           std::initializer_list<std::string> Names,
           const Kind &K,
           KindExactness Exactness = KindExactness::Exact) {
    ContainersStatus[Name].emplace_back(Names, K, Exactness);
  }

  void add(llvm::StringRef Name, AutoEnforcerTarget Target) {
    ContainersStatus[Name].emplace_back(std::move(Target));
  }

  bool contains(llvm::StringRef ContainerName) const {
    return ContainersStatus.find(ContainerName) != ContainersStatus.end();
  }

  template<typename OStream>
  void dump(OStream &OS, size_t Indents = 0) const {
    indent(OS, Indents);
    OS << "{\n";
    for (const auto &Container : ContainersStatus) {
      indent(OS, Indents + 1);
      OS << Container.first().str() << ":\n";
      for (const auto &Entry : Container.second)
        Entry.dump(OS, Indents + 2);
    }
    indent(OS, Indents);
    OS << "}\n";
  }

  iterator find(llvm::StringRef ContainerName) {
    return ContainersStatus.find(ContainerName);
  }

  const_iterator find(llvm::StringRef ContainerName) const {
    return ContainersStatus.find(ContainerName);
  }

  void dump() const debug_function { dump(dbg); }

  void merge(const BackingContainersStatus &Other);

  void removeDupplicates();

private:
  Container ContainersStatus;
};

template<typename KindDictionary>
llvm::Error parseAutoEnforcerTarget(BackingContainersStatus &CurrentStatus,
                                    llvm::StringRef AsString,
                                    const KindDictionary &Dict) {
  llvm::SmallVector<llvm::StringRef, 2> Parts;
  AsString.split(Parts, ':', 1);

  if (Parts.size() != 2)
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "string %s was not in expected form "
                                   "<BackingContainerName:AutoEnforcerTarget>",
                                   AsString.str().c_str());

  auto MaybeTarget = parseAutoEnforcerTarget(Parts[1], Dict);
  if (not MaybeTarget)
    return MaybeTarget.takeError();

  CurrentStatus.add(Parts[0], std::move(*MaybeTarget));
  return llvm::Error::success();
}

} // namespace AutoEnforcer
