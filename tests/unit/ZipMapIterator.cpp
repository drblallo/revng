/// \file ZipMapIterator.cpp
/// \brief Tests for ZipMapIterator

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <iterator>
#include <map>
#include <set>

#define BOOST_TEST_MODULE ZipMapIterator
bool init_unit_test();
#include "boost/test/unit_test.hpp"

#include "revng/ADT/MutableSet.h"
#include "revng/ADT/STLExtras.h"
#include "revng/ADT/SmallMap.h"
#include "revng/ADT/SortedVector.h"
#include "revng/ADT/ZipMapIterator.h"
#include "revng/UnitTestHelpers/UnitTestHelpers.h"

// Local includes
#include "TestKeyedObject.h"

using namespace llvm;

template<typename T, typename = void>
struct KeyContainer {};

template<typename T>
struct KeyContainer<T, enable_if_is_map_like_t<T>> {
  using key_type = typename T::key_type;

  static void insert(T &Container, typename T::key_type Key) {
    Container.insert({ Key, typename T::mapped_type() });
  }

  static auto find(T &Container, typename T::key_type &Key) {
    return &*Container.find(Key);
  }

  static void sort(T &) {}
};

template<typename T>
struct KeyContainer<
  T,
  std::enable_if_t<is_set_like_v<T> or is_KeyedObjectContainer_v<T>>> {
  using key_type = const typename T::key_type;

  static void insert(T &Container, key_type Key) { Container.insert(Key); }

  static auto find(T &Container, key_type Key) { return &*Container.find(Key); }

  static void sort(T &) {}
};

template<typename T>
struct KeyContainer<T,
                    typename std::enable_if_t<is_vector_of_pairs<T>::value>> {
  using key_type = typename T::value_type::first_type;
  using value_type = std::conditional_t<std::is_const<T>::value,
                                        const typename T::value_type,
                                        typename T::value_type>;
  using mapped_type = typename value_type::second_type;

  static void insert(T &Container, key_type Key) {
    Container.push_back({ Key, mapped_type() });
  }

  static auto find(T &Container, key_type Key) {
    auto Condition = [Key](const value_type &Value) {
      return Value.first == Key;
    };
    return &*std::find_if(Container.begin(), Container.end(), Condition);
  }

  static void sort(T &Container) {
    static_assert(not std::is_const<T>::value, "");
    using non_const_value_type = std::pair<std::remove_const_t<key_type>,
                                           mapped_type>;
    auto Less = [](const non_const_value_type &This,
                   const non_const_value_type &Other) {
      return This.first < Other.first;
    };
    using vector = std::vector<non_const_value_type>;
    auto &NonConst = *reinterpret_cast<vector *>(&Container);
    std::sort(NonConst.begin(), NonConst.end(), Less);
  }
};

template<typename T>
static void
compare(T &Left,
        T &Right,
        std::vector<std::pair<Optional<int>, Optional<int>>> &&Expected) {
  using KE = KeyContainer<T>;
  using pointer = element_pointer_t<T>;
  std::vector<std::pair<pointer, pointer>> Result;
  std::copy(zipmap_begin(Left, Right),
            zipmap_end(Left, Right),
            std::back_inserter(Result));

  revng_check(Result.size() == Expected.size());

  auto FindLeft = [&Expected, &Left](unsigned I) {
    return Expected[I].first ? KE::find(Left, *Expected[I].first) : nullptr;
  };

  auto FindRight = [&Expected, &Right](unsigned I) {
    return Expected[I].second ? KE::find(Right, *Expected[I].second) : nullptr;
  };

  for (unsigned I = 0; I < Result.size(); I++) {
    std::pair<pointer, pointer> X{ FindLeft(I), FindRight(I) };
    revng_check(Result[I] == X);
  }
}

template<typename Map>
void run() {
  Map A, B;
  const Map &ARef = A;
  const Map &BRef = B;

  using KC = KeyContainer<Map>;

  KC::insert(A, 1);
  KC::insert(A, 2);
  KC::insert(A, 4);
  KC::insert(A, 5);
  KC::sort(A);

  KC::insert(B, 1);
  KC::insert(B, 3);
  KC::insert(B, 4);
  KC::insert(B, 7);
  KC::sort(B);

  compare(ARef,
          BRef,
          {
            { { 1 }, { 1 } },
            { { 2 }, {} },
            { {}, { 3 } },
            { { 4 }, { 4 } },
            { { 5 }, {} },
            { {}, { 7 } },
          });

  KC::insert(A, 0);
  KC::sort(A);
  compare(A,
          B,
          {
            { { 0 }, {} },
            { { 1 }, { 1 } },
            { { 2 }, {} },
            { {}, { 3 } },
            { { 4 }, { 4 } },
            { { 5 }, {} },
            { {}, { 7 } },
          });

  KC::insert(B, -1);
  KC::sort(B);
  compare(A,
          B,
          {
            { {}, { -1 } },
            { { 0 }, {} },
            { { 1 }, { 1 } },
            { { 2 }, {} },
            { {}, { 3 } },
            { { 4 }, { 4 } },
            { { 5 }, {} },
            { {}, { 7 } },
          });
}

BOOST_AUTO_TEST_CASE(TestStdMap) {
  run<std::map<int, long>>();
}

BOOST_AUTO_TEST_CASE(TestStdSet) {
  run<std::set<int>>();
}

BOOST_AUTO_TEST_CASE(TestMutableSet) {
  run<MutableSet<int>>();
}

BOOST_AUTO_TEST_CASE(TestSortedVector) {
  run<SortedVector<int>>();
}

BOOST_AUTO_TEST_CASE(TestStdVectorPair) {
  run<std::vector<std::pair<const int, long>>>();
}

BOOST_AUTO_TEST_CASE(TestSmallMap) {
  run<SmallMap<int, long, 4>>();
}
