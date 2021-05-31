#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// WIP: reduce headers
#include "revng/AutoEnforcer/AutoEnforcerTarget.h"
#include "revng/AutoEnforcer/BackingContainers.h"
#include "revng/AutoEnforcer/InputOutputContract.h"
#include "revng/Enforcers/RevngEnforcers.h"
#include "revng/AutoEnforcer/LLVMEnforcer.h"

namespace AutoEnforcer {

class CompileModuleEnforcer {
public:
  static constexpr auto Name = "Compile Module Enforcer";
  std::array<InputOutputContract, 1> getContract() const {
    return {
      InputOutputContract(Root, KindExactness::DerivedFrom, 0, Object, 1, true)
    };
  }
  void run(DefaultLLVMContainer &TargetContainer, BinaryContainer &TargetBinary);
};

}
