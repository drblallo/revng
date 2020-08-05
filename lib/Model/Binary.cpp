/// \file Binary.cpp
/// \brief

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// Local libraries includes
#include "revng/Model/Binary.h"

using namespace llvm;

using BasicBlockRangeVector = std::vector<std::pair<MetaAddress, MetaAddress>>;
using CFGVector = decltype(model::Function::CFG);

namespace model {

static void processEdge(BasicBlockRangeVector &Result,
                        const CFGVector &CFG,
                        const FunctionEdge &Edge) {
  using namespace model::FunctionEdgeType;
  switch (Edge.Type) {
  case Invalid:
    revng_abort();
    break;

  case FakeFunctionCall:
  case FakeFunctionReturn:
  case FunctionCall:
  case IndirectCall:
  case Return:
  case BrokenReturn:
  case IndirectTailCall:
  case LongJmp:
  case Killer:
  case Unreachable:
    // Ignore all non-direct branches
    return;

  case DirectBranch:
    break;
  }

  // Find the next edge in the list
  FunctionEdge NextEdge{ Edge.Destination, MetaAddress::invalid(), Invalid };
  auto NextIt = CFG.lower_bound(NextEdge);
  revng_assert(NextIt != CFG.end());

  MetaAddress BlockEnd = NextIt->Source;

  // Record the basic block
  Result.emplace_back(Edge.Destination, BlockEnd);
}

BasicBlockRangeVector Function::basicBlockRanges() const {
  BasicBlockRangeVector Result;

  //
  // Populate Result with all the basic block start addresses
  //

  // Add the entry point (a "virtual" edge into the entry address)
  using namespace model::FunctionEdgeType;
  processEdge(Result, CFG, { MetaAddress::invalid(), Entry, Invalid });

  // Add all the other entries found in the CFG
  for (const auto &Edge : CFG)
    processEdge(Result, CFG, Edge);

  //
  // Identify the end address of each identified basic block
  //

  //
  // Sort the results, except for the first one
  //
  std::sort(++Result.begin(), Result.end());

  return Result;
}

} // namespace model
