#ifndef SUPPORT_YAMLTRAITS_H
#define SUPPORT_YAMLTRAITS_H

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// LLVM includes
#include "llvm/Support/YAMLTraits.h"

namespace detail {

using namespace llvm::yaml;

template<typename T>
using has_MappingTraits = has_MappingTraits<T, EmptyContext>;

template<typename T, typename K = void>
using ei_hmt = std::enable_if_t<has_MappingTraits<T>::value, K>;
} // namespace detail

template<typename T, typename K = void>
using enable_if_has_MappingTraits = detail::ei_hmt<T, K>;

#endif // SUPPORT_YAMLTRAITS_H
