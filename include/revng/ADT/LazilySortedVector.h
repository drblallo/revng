#ifndef LAZILYSORTEDVECTOR_H
#define LAZILYSORTEDVECTOR_H

// LLVM includes
#include "llvm/ADT/STLExtras.h"

// Local libraries includes
#include "revng/ADT/KeyTraits.h"

template<typename T>
class SortedVector {
private:
  using key_type_internal = decltype(std::declval<T>().key());
  using inner_key_type = const typename KeyTraits<key_type_internal>::IntsArray;
  using vector_type = std::vector<T>;

public:
  using key_type = const key_type_internal;
  using size_type = typename vector_type::size_type;
  using mapped_type = T;
  using value_type = typename vector_type::value_type;
  using difference_type = typename vector_type::difference_type;
  using allocator_type = typename vector_type::allocator_type;
  using reference = typename vector_type::reference;
  using const_reference = typename vector_type::const_reference;
  using pointer = typename vector_type::pointer;
  using const_pointer = typename vector_type::const_pointer;

private:
  using iterator = typename vector_type::iterator;
  using const_iterator = typename vector_type::const_iterator;
  using reverse_iterator = typename vector_type::reverse_iterator;
  using const_reverse_iterator = typename vector_type::const_reverse_iterator;

private:
  mutable bool IsSorted;
  mutable vector_type TheVector;

public:
  T &at(const key_type &Key) {
    auto It = find(Key);
    revng_assert(It != end());
    return *It;
  }

  const T &at(const key_type &Key) const {
    auto It = find(Key);
    revng_assert(It != end());
    return *It;
  }

  T &operator[](const key_type &Key) {
    auto It = find(Key);
    if (It != end()) {
      return *It;
    } else {
      TheVector.emplace_back(Key);
      return TheVector.back();
    }
  }

  T &operator[](key_type &&Key) {
    auto It = find(Key);
    if (It != end()) {
      return *It;
    } else {
      TheVector.emplace_back(Key);
      IsSorted = false;
      return TheVector.back();
    }
  }

  iterator begin() {
    sort();
    return TheVector.begin();
  }
  iterator end() {
    sort();
    return TheVector.end();
  }
  const_iterator begin() const {
    sort();
    return TheVector.begin();
  }
  const_iterator end() const {
    sort();
    return TheVector.end();
  }
  const_iterator cbegin() const {
    sort();
    return TheVector.cbegin();
  }
  const_iterator cend() const {
    sort();
    return TheVector.cend();
  }
  reverse_iterator rbegin() {
    sort();
    return TheVector.rbegin();
  }
  reverse_iterator rend() {
    sort();
    return TheVector.rend();
  }
  const_reverse_iterator rbegin() const {
    sort();
    return TheVector.rbegin();
  }
  const_reverse_iterator rend() const {
    sort();
    return TheVector.rend();
  }
  const_reverse_iterator crbegin() const {
    sort();
    return TheVector.crbegin();
  }
  const_reverse_iterator crend() const {
    sort();
    return TheVector.crend();
  }

  bool empty() const { return TheVector.empty(); }
  size_type size() const { return TheVector.size(); }
  size_type max_size() const { return TheVector.max_size(); }
  void clear() { TheVector.clear(); }
  void reserve(size_type NewSize) { TheVector.reserve(NewSize); }
  size_type capacity() const { return TheVector.capacity(); }

  /// \note Use with caution
  void push_back(const T &Value) {
    IsSorted = false;
#ifndef NDEBUG
    using KeyTraits = KeyTraits<key_type_internal>;
    auto ValueKey = KeyTraits::toInts(Value.key());
    auto Compare = [&ValueKey](const T &V) {
      return KeyTraits::toInts(V.key()) == ValueKey;
    };
    auto End = TheVector.end();
    revng_assert(std::find_if(TheVector.begin(), End, Compare) == End);
#endif
    TheVector.push_back(Value);
  }

  std::pair<iterator, bool> insert(const T &Value) {
    auto It = find(Value.key());
    if (It != end())
      return { It, false };

    TheVector.push_back(Value);
    IsSorted = false;
    sort();

    return { --TheVector.end(), true };
  }

  iterator erase(iterator Pos) {
    revng_assert(IsSorted);
    return TheVector.erase(Pos);
  }
  iterator erase(const_iterator First, const_iterator Last) {
    revng_assert(IsSorted);
    return TheVector.erase(First, Last);
  }

  size_type erase(const key_type &Key) {
    auto It = find(Key);
    if (It == end()) {
      return 0;
    } else {
      erase(It);
      return 1;
    }
  }

  void swap(SortedVector &Other) {
    std::swap(IsSorted, Other.IsSorted);
    TheVector.swap(Other.TheVector);
  }

  size_type count(const key_type &Key) const {
    return find(Key) != end() ? 1 : 0;
  }

  iterator find(const key_type &Key) {
    using KeyTraits = KeyTraits<key_type_internal>;
    auto It = lower_bound(Key);
    auto End = end();
    if (!(It == End)
        and KeyTraits::toInts(Key) < KeyTraits::toInts(It->key())) {
      return End;
    } else {
      return It;
    }
  }

  const_iterator find(const key_type &Key) const {
    using KeyTraits = KeyTraits<key_type_internal>;
    auto It = lower_bound(Key);
    auto End = end();
    if (!(It == End)
        and KeyTraits::toInts(Key) < KeyTraits::toInts(It->key())) {
      return End;
    } else {
      return It;
    }
  }

  iterator lower_bound(const key_type &Key) {
    sort();
    auto TargetInts = KeyTraits<key_type_internal>::toInts(Key);
    auto Compare = [](const T &LHS, const T &RHS) {
      using KeyTraits = KeyTraits<key_type_internal>;
      return KeyTraits::toInts(LHS.key()) < KeyTraits::toInts(RHS.key());
    };
    return std::lower_bound(TheVector.begin(), TheVector.end(), Key, Compare);
  }

  const_iterator lower_bound(const key_type &Key) const {
    sort();
    auto TargetInts = KeyTraits<key_type_internal>::toInts(Key);
    auto Compare = [](const T &LHS, const T &RHS) {
      using KeyTraits = KeyTraits<key_type_internal>;
      return KeyTraits::toInts(LHS.key()) < KeyTraits::toInts(RHS.key());
    };
    return std::lower_bound(TheVector.begin(), TheVector.end(), Key, Compare);
  }

  iterator upper_bound(const key_type &Key) {
    sort();
    auto TargetInts = KeyTraits<key_type_internal>::toInts(Key);
    auto Compare = [](const T &LHS, const T &RHS) {
      using KeyTraits = KeyTraits<key_type_internal>;
      return KeyTraits::toInts(LHS.key()) < KeyTraits::toInts(RHS.key());
    };
    return std::upper_bound(TheVector.begin(), TheVector.end(), Key, Compare);
  }

  const_iterator upper_bound(const key_type &Key) const {
    sort();
    auto TargetInts = KeyTraits<key_type_internal>::toInts(Key);
    // WIP: factor out
    auto Compare = [](const T &LHS, const T &RHS) {
      using KeyTraits = KeyTraits<key_type_internal>;
      return KeyTraits::toInts(LHS.key()) < KeyTraits::toInts(RHS.key());
    };
    return std::upper_bound(TheVector.begin(), TheVector.end(), Key, Compare);
  }

  void sort() const {
    if (not IsSorted) {
      auto Compare = [](const T &LHS, const T &RHS) {
        using KeyTraits = KeyTraits<key_type_internal>;
        return KeyTraits::toInts(LHS.key()) < KeyTraits::toInts(RHS.key());
      };
      std::sort(TheVector.begin(), TheVector.end(), Compare);
      IsSorted = true;
    }
  }
};

#endif // LAZILYSORTEDVECTOR_H
