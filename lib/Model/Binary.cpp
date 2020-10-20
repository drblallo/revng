/// \file Binary.cpp
/// \brief

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// Local libraries includes
#include "revng/Model/Binary.h"

using namespace llvm;

using BasicBlockRangesMap = std::map<MetaAddress, MetaAddress>;
using BasicBlockRangesVector = std::vector<std::pair<MetaAddress, MetaAddress>>;
using CFGVector = decltype(model::Function::CFG);

namespace model {

static void processEdge(BasicBlockRangesMap &Ranges,
                        const CFGVector &CFG,
                        const FunctionEdge &Edge) {

  if (Ranges.count(Edge.Destination) != 0)
    return;

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
  Ranges[Edge.Destination] = BlockEnd;
}

BasicBlockRangesVector Function::basicBlockRanges() const {
  BasicBlockRangesMap Ranges;

  //
  // Populate Result with all the basic block start addresses
  //

  // Add the entry point (a "virtual" edge into the entry address)
  using namespace model::FunctionEdgeType;
  processEdge(Ranges, CFG, { MetaAddress::invalid(), Entry, DirectBranch });

  // Add all the other entries found in the CFG
  for (const auto &Edge : CFG)
    processEdge(Ranges, CFG, Edge);

  //
  // Compose the result
  //
  BasicBlockRangesVector Result;

  // Ensure the first element of Result is the entry blcok
  auto It = Ranges.find(Entry);
  revng_assert(It != Ranges.end());
  Result.push_back(*It);

  // Remove the entry block
  Ranges.erase(It);

  // Append all the other blocks
  for (const auto &[Start, End] : Ranges)
    Result.emplace_back(Start, End);

  return Result;
}

} // namespace model

namespace model {

bool Function::verifyCFG() const {
#if 0
  // Make sure that the target of each DirectBranch edge is the source of
  // another edge
  {
    std::set<MetaAddress> Sources;
    std::set<MetaAddress> Destinations;
    for (const FunctionEdge &Edge : CFG) {
      Sources.insert(Edge.Source);
      Destinations.insert(Edge.Destination);
    }

    for (const FunctionEdge &Edge : CFG) {
      if (Edge.Type == FunctionEdgeType::DirectBranch) {
        if (Sources.count(Edge.Destination) == 0) {
          llvm::errs() << "Function " << Name << " (" << Entry.toString() << ")"
                       << " has a DirectBranch jumping from "
                       << Edge.Source.toString()
                       << " to " << Edge.Destination.toString()
                       << " but no other edge leaves from there\n";
          return false;
        } else if (Edge.Source Destinations.count(Edge.Source)) {
        }
      }
    }
  }
#endif
  return true;
}

} // namespace model
