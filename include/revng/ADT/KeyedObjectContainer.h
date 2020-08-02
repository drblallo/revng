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
namespace detail {

template<typename T>
using no_cv_t = std::remove_cv_t<T>;

template<typename T, template<typename...> class Ref>
constexpr bool is_no_cv_specialization_v = is_specialization_v<no_cv_t<T>, Ref>;

template<typename T>
constexpr bool is_mutableset_v = is_no_cv_specialization_v<T, MutableSet>;

template<typename T>
constexpr bool is_sortedvector_v = is_no_cv_specialization_v<T, SortedVector>;

template<typename T>
constexpr bool is_KOC_v = is_mutableset_v<T> or is_sortedvector_v<T>;

template<typename T, typename K = void>
using enable_if_is_KOC_t = std::enable_if_t<is_KOC_v<T>, K>;

} // namespace detail

template<typename T>
constexpr bool is_KeyedObjectContainer_v = detail::is_KOC_v<T>;

template<typename T, typename K = void>
using enable_if_is_KeyedObjectContainer_t = detail::enable_if_is_KOC_t<T, K>;

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
        using KOT = KeyedObjectTraits<value_type>;
        using key_type = decltype(KOT::key(std::declval<value_type>()));
        value_type Instance = KOT::fromKey(key_type());
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
