#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <iterator>
#include <set>
#include <tuple>
#include <vector>

#include "llvm/ADT/Optional.h"
#include "llvm/ADT/iterator.h"

#include "revng/ADT/KeyedObjectContainer.h"
#include "revng/Support/Assert.h"

//
// has_mapped_type_member
//

namespace detail {

template<typename T>
using eit_mt_t = typename enable_if_type<typename T::mapped_type>::type;

template<typename T>
using eit_vt_t = typename enable_if_type<typename T::value_type>::type;

} // namespace detail

template<class T, class Enable = void>
struct has_mapped_type_member : std::false_type {};

template<class T>
struct has_mapped_type_member<T, detail::eit_mt_t<T>> : std::true_type {};

//
// has_value_type_member
//
template<class T, class Enable = void>
struct has_value_type_member : std::false_type {};
template<class T>
struct has_value_type_member<T, detail::eit_vt_t<T>> : std::true_type {};

//
// has_key_type_member
//
template<class T, class Enable = void>
struct has_key_type_member : std::false_type {};
template<class T>
struct has_key_type_member<T,
                           typename enable_if_type<typename T::key_type>::type>
  : std::true_type {};

//
// is_map_like
//
template<typename T>
constexpr bool is_map_like_v = (has_value_type_member<T>::value
                                and has_key_type_member<T>::value
                                and has_mapped_type_member<T>::value);

template<typename T, typename K = void>
using enable_if_is_map_like_t = std::enable_if_t<is_map_like_v<T>, K>;

//
// is_set_like
//
namespace detail {
template<typename T>
constexpr bool same_key_value_v = std::is_same_v<typename T::key_type,
                                                 typename T::value_type>;
}

template<class T, class Enable = void>
struct same_key_value_types : std::false_type {};

namespace detail {

template<typename T>
using ei_skv_t = std::enable_if_t<
  std::is_same_v<typename T::key_type, typename T::value_type>>;
}

template<class T>
struct same_key_value_types<T, detail::ei_skv_t<T>> : std::true_type {};

template<typename T>
constexpr bool is_set_like_v = (has_value_type_member<T>::value
                                and has_key_type_member<T>::value
                                and not has_mapped_type_member<T>::value
                                and same_key_value_types<T>::value);

template<typename T, typename K = void>
using enable_if_is_set_like_t = std::enable_if_t<is_set_like_v<T>, K>;

//
// is_vector_of_pairs
//
template<typename>
struct is_vector_of_pairs : public std::false_type {};

template<typename K, typename V>
struct is_vector_of_pairs<std::vector<std::pair<const K, V>>>
  : public std::true_type {};

template<typename K, typename V>
struct is_vector_of_pairs<const std::vector<std::pair<const K, V>>>
  : public std::true_type {};

namespace {

using namespace std;

static_assert(is_vector_of_pairs<vector<pair<const int, long>>>::value, "");
static_assert(is_vector_of_pairs<const vector<pair<const int, long>>>::value,
              "");

} // namespace

//
// element_pointer_t
//
template<typename T>
using element_pointer_t = decltype(&*std::declval<T>().begin());

template<typename T>
enable_if_is_set_like_t<T, const typename T::key_type &>
keyFromValue(const typename T::value_type &Value) {
  return Value;
}

template<typename T>
enable_if_is_KeyedObjectContainer_t<T, typename T::key_type>
keyFromValue(const typename T::value_type &Value) {
  return KeyedObjectTraits<typename T::value_type>::key(Value);
}

template<typename T>
std::enable_if_t<is_vector_of_pairs<T>::value,
                 const typename T::value_type::first_type &>
keyFromValue(const typename T::value_type &Value) {
  return Value.first;
}

template<typename T>
enable_if_is_map_like_t<T, const typename T::value_type::first_type &>
keyFromValue(const typename T::value_type &Value) {
  return Value.first;
}

template<typename Map>
struct DefaultComparator {
  template<typename T>
  static int compare(const T &LHS, const T &RHS) {
    auto LHSKey = keyFromValue<Map>(LHS);
    auto RHSKey = keyFromValue<Map>(RHS);
    auto Less = std::less<decltype(LHSKey)>();
    if (Less(LHSKey, RHSKey))
      return -1;
    else if (Less(RHSKey, LHSKey))
      return 1;
    else
      return 0;
  }
};

template<typename Map, typename Comparator = DefaultComparator<Map>>
using zipmap_pair = std::pair<element_pointer_t<Map>, element_pointer_t<Map>>;

template<typename Map, typename Comparator = DefaultComparator<Map>>
class ZipMapIterator
  : public llvm::iterator_facade_base<ZipMapIterator<Map, Comparator>,
                                      std::forward_iterator_tag,
                                      const zipmap_pair<Map, Comparator>> {
public:
  template<bool C, typename A, typename B>
  using conditional_t = typename std::conditional<C, A, B>::type;
  using inner_iterator = conditional_t<std::is_const<Map>::value,
                                       typename Map::const_iterator,
                                       typename Map::iterator>;
  using inner_range = llvm::iterator_range<inner_iterator>;
  using value_type = zipmap_pair<Map, Comparator>;
  using reference = typename ZipMapIterator::reference;

private:
  value_type Current;
  inner_iterator LeftIt;
  const inner_iterator EndLeftIt;
  inner_iterator RightIt;
  const inner_iterator EndRightIt;

public:
  ZipMapIterator(inner_range LeftRange, inner_range RightRange) :
    LeftIt(LeftRange.begin()),
    EndLeftIt(LeftRange.end()),
    RightIt(RightRange.begin()),
    EndRightIt(RightRange.end()) {

    next();
  }

  ZipMapIterator(inner_iterator LeftIt, inner_iterator RightIt) :
    ZipMapIterator(llvm::make_range(LeftIt, LeftIt),
                   llvm::make_range(RightIt, RightIt)) {}

  bool operator==(const ZipMapIterator &Other) const {
    revng_assert(EndLeftIt == Other.EndLeftIt);
    revng_assert(EndRightIt == Other.EndRightIt);
    auto ThisTie = std::tie(LeftIt, RightIt, Current);
    auto OtherTie = std::tie(Other.LeftIt, Other.RightIt, Other.Current);
    return ThisTie == OtherTie;
  }

  ZipMapIterator &operator++() {
    next();
    return *this;
  }

  reference operator*() const { return Current; }

private:
  bool leftIsValid() const { return LeftIt != EndLeftIt; }
  bool rightIsValid() const { return RightIt != EndRightIt; }

  void next() {
    if (leftIsValid() and rightIsValid()) {
      switch (Comparator::compare(*LeftIt, *RightIt)) {
      case 0:
        Current = decltype(Current)(&*LeftIt, &*RightIt);
        LeftIt++;
        RightIt++;
        break;

      case -1:
        Current = std::make_pair(&*LeftIt, nullptr);
        LeftIt++;
        break;

      case 1:
        Current = std::make_pair(nullptr, &*RightIt);
        RightIt++;
        break;

      default:
        revng_abort();
      }
    } else if (leftIsValid()) {
      Current = std::make_pair(&*LeftIt, nullptr);
      LeftIt++;
    } else if (rightIsValid()) {
      Current = std::make_pair(nullptr, &*RightIt);
      RightIt++;
    } else {
      Current = std::make_pair(nullptr, nullptr);
    }
  }
};

template<typename T, typename Comparator = DefaultComparator<T>>
inline ZipMapIterator<T, Comparator> zipmap_begin(T &Left, T &Right) {
  return ZipMapIterator<T, Comparator>(llvm::make_range(Left.begin(),
                                                        Left.end()),
                                       llvm::make_range(Right.begin(),
                                                        Right.end()));
}

template<typename T, typename Comparator = DefaultComparator<T>>
inline ZipMapIterator<T, Comparator> zipmap_end(T &Left, T &Right) {
  return ZipMapIterator<T, Comparator>(llvm::make_range(Left.end(), Left.end()),
                                       llvm::make_range(Right.end(),
                                                        Right.end()));
}

template<typename T, typename Comparator = DefaultComparator<T>>
inline llvm::iterator_range<ZipMapIterator<T, Comparator>>
zipmap_range(T &Left, T &Right) {
  return llvm::make_range(zipmap_begin<T, Comparator>(Left, Right),
                          zipmap_end<T, Comparator>(Left, Right));
}
