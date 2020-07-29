#ifndef KEYEDOBJECTTRAITS_H
#define KEYEDOBJECTTRAITS_H

// Local libraries includes
#include "revng/ADT/STLExtras.h"

template<typename T, typename = void>
struct KeyedObjectTraits {
  // static * key(const T &);
  // static T fromKey(* Key);
};

/// Inherit if T is the key of itself
template<typename T>
struct IdentityKeyedObjectTraits {
  static T key(const T &Obj) { return Obj; }

  static T fromKey(T Obj) { return Obj; }
};

/// Trivial specialization for integral types
template<typename T>
struct KeyedObjectTraits<T, enable_if_is_integral_t<T>>
  : public IdentityKeyedObjectTraits<T> {};

#endif // KEYEDOBJECTTRAITS_H
