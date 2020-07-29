#ifndef KEYEDOBJECTCONTAINER_H
#define KEYEDOBJECTCONTAINER_H

// LLVM includes
#include "llvm/Support/YAMLTraits.h"

// Local libraries includes
#include "revng/ADT/KeyedObjectTraits.h"
#include "revng/ADT/STLExtras.h"

template<typename T>
class MutableSet;

template<typename T>
class SortedVector;

//
// is_KeyedObjectContainer
//
template<typename T>
constexpr bool is_KeyedObjectContainer_v =
  (is_specialization_v<
     std::remove_cv_t<T>,
     MutableSet> or is_specialization_v<std::remove_cv_t<T>, SortedVector>);

template<typename T, typename K = void>
using enable_if_is_KeyedObjectContainer_t = std::
  enable_if_t<is_KeyedObjectContainer_v<T>, K>;

static_assert(is_KeyedObjectContainer_v<MutableSet<int>>);
static_assert(is_KeyedObjectContainer_v<SortedVector<int>>);

namespace llvm::yaml {

template<typename T, typename Context>
enable_if_is_KeyedObjectContainer_t<T>
yamlize(llvm::yaml::IO &io, T &Seq, bool, Context &Ctx) {
  unsigned InputCount = io.beginSequence();

  if (io.outputting()) {
    unsigned I = 0;
    for (auto &Element : Seq) {
      void *SaveInfo;
      if (io.preflightElement(I, SaveInfo)) {
        yamlize(io, Element, true, Ctx);
        io.postflightElement(SaveInfo);
      }
      ++I;
    }
  } else {
    auto Inserter = Seq.batch_insert();
    for (unsigned I = 0; I < InputCount; ++I) {
      void *SaveInfo;
      if (io.preflightElement(I, SaveInfo)) {
        using value_type = typename T::value_type;
        using key_type = decltype(
          KeyedObjectTraits<value_type>::key(std::declval<value_type>()));
        value_type Instance = KeyedObjectTraits<value_type>::fromKey(
          key_type());
        yamlize(io, Instance, true, Ctx);
        Inserter.insert(Instance);
        io.postflightElement(SaveInfo);
      }
    }
  }

  io.endSequence();
}

} // namespace llvm::yaml

#endif // KEYEDOBJECTCONTAINER_H
