#ifndef SUPPORT_METAADDRESS_KEYTRAITS_H
#define SUPPORT_METAADDRESS_KEYTRAITS_H

// Standard includes
#include <array>
#include <cstdint>
#include <string>

// Local libraries includes
#include "revng/Support/MetaAddress.h"

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

#endif // SUPPORT_METAADDRESS_KEYTRAITS_H
