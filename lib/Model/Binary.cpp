/// \file Binary.cpp
/// \brief

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// LLVM includes
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/raw_os_ostream.h"

// Local libraries includes
#include "revng/ADT/GenericGraph.h"
#include "revng/Model/Binary.h"

using namespace llvm;

using BasicBlockRangesMap = std::map<MetaAddress, MetaAddress>;
using BasicBlockRangesVector = std::vector<std::pair<MetaAddress, MetaAddress>>;
using CFGVector = decltype(model::Function::CFG);

namespace model {

#if 0
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
#endif

BasicBlockRangesVector Function::basicBlockRanges() const {

  BasicBlockRangesVector Result;
  for (const model::BasicBlock &BB : CFG) {
    Result.emplace_back(BB.Start, BB.End);
  }
  return Result;

#if 0
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
#endif
}

} // namespace model

namespace model {

struct FunctionCFGNode : public ForwardNode<FunctionCFGNode, Empty, false> {
  FunctionCFGNode(MetaAddress Start) : Start(Start) {}
  MetaAddress Start;
};

struct FunctionCFG : public GenericGraph<FunctionCFGNode> {
public:
  FunctionCFG(MetaAddress Entry) : Entry(Entry) {}

public:
  MetaAddress entry() const { return Entry; }
  FunctionCFGNode *entryNode() const { return Map.at(Entry); }

public:
  FunctionCFGNode *get(MetaAddress MA) {
    FunctionCFGNode *Result = nullptr;
    auto It = Map.find(MA);
    if (It == Map.end()) {
      Result = addNode(MA);
      Map[MA] = Result;
    } else {
      Result = It->second;
    }

    return Result;
  }

  bool allNodesAreReachable() const {
    if (Map.size() == 0)
      return true;

    // Ensure all the nodes are reachable from the entry node
    df_iterator_default_set<FunctionCFGNode *> Visited;
    for (auto &Ignore : depth_first_ext(entryNode(), Visited))
      ;
    return Visited.size() == size();
  }

  bool hasOnlyInvalidExits() const {
    for (auto &[Address, Node] : Map)
      if (Address.isValid() and not Node->hasSuccessors())
        return false;
    return true;
  }

private:
  MetaAddress Entry;
  std::map<MetaAddress, FunctionCFGNode *> Map;
};

bool Function::verifyCFG() const {
  using namespace FunctionEdgeType;

  yaml::Output YAMLOutput(llvm::errs());
  YAMLOutput << *const_cast<Function *>(this);

#if 0
  std::map<MetaAddress, MetaAddress> EndToStart;
  {
    std::set<MetaAddress> BlockAddresses { Entry };
    for (const FunctionEdge &Edge : CFG) {

      switch (Edge.Type) {
      case DirectBranch:
      case FakeFunctionCall:
      case FakeFunctionReturn:
      case Return:
      case BrokenReturn:
      case IndirectTailCall:
      case LongJmp:
      case Unreachable:
        if (Edge.Destination.isValid())
          BlockAddresses.insert(Edge.Destination);
        break;

      case FunctionCall:
      case IndirectCall:
        revng_assert(Edge.Source.isValid());
        BlockAddresses.insert(Edge.Source);
        break;

      case Killer:
        break;

      case Invalid:
        revng_abort();
        break;
      }

    }

    for (const FunctionEdge &Edge : CFG) {
      // Find the closest BlockAddress
      auto It = BlockAddresses.lower_bound(Edge.Source);
      revng_assert(It != BlockAddresses.begin());
      --It;
      EndToStart[Edge.Source] = *It;
    }
  }
#endif

  // Populate graph
  FunctionCFG Graph(Entry);
  for (const BasicBlock &Block : CFG) {
    auto *Source = Graph.get(Block.Start);

    for (const FunctionEdge &Edge : Block.Successors) {
      switch (Edge.Type) {
      case DirectBranch:
      case FakeFunctionCall:
      case FakeFunctionReturn:
      case Return:
      case BrokenReturn:
      case IndirectTailCall:
      case LongJmp:
      case Unreachable:
        Source->addSuccessor(Graph.get(Edge.Destination));
        break;

      case FunctionCall:
      case IndirectCall:
        Source->addSuccessor(Graph.get(Block.End));
        break;

      case Killer:
        Source->addSuccessor(Graph.get(MetaAddress::invalid()));
        break;

      case Invalid:
        revng_abort();
        break;
      }
    }
  }

  {
    raw_os_ostream Output(dbg);
    WriteGraph(Output, &Graph);
  }

  // Ensure all the nodes are reachable from the entry node
  revng_assert(Graph.allNodesAreReachable());

  // Ensure the only node with no successors is invalid
  revng_assert(Graph.hasOnlyInvalidExits());

  return true;
}

} // namespace model

template<>
struct llvm::DOTGraphTraits<model::FunctionCFG *>
  : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool simple = false) : DefaultDOTGraphTraits(simple) {}

  static std::string
  getNodeLabel(const model::FunctionCFGNode *Node, const model::FunctionCFG *) {
    return Node->Start.toString();
  }

  static std::string getNodeAttributes(const model::FunctionCFGNode *Node,
                                       const model::FunctionCFG *Graph) {
    if (Node->Start == Graph->entry()) {
      return "shape=box,peripheries=2";
    }

    return "";
  }
};
