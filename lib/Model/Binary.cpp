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

// TODO: implement removeSuccessor
// TODO: implement addPredecessor
// TODO: implement version with edges
// WIP: implement graph traits

struct Lel {};

template<typename Inheritor,
         typename NeighborContainer = std::vector<Inheritor *>>
class ForwardNode {
public:
  using child_iterator = typename NeighborContainer::iterator;
  using const_child_iterator = typename NeighborContainer::const_iterator;

public:
  void addSuccessor(Inheritor *NewSuccessor) {
    Successors.push_back(NewSuccessor);
  }

  auto successors() const {
    return llvm::make_range(Successors.begin(), Successors.end());
  }

  auto successors() {
    return llvm::make_range(Successors.begin(), Successors.end());
  }

private:
  NeighborContainer Successors;

};

template<typename Node,
         template<typename...> class NodesContainer = std::vector>
class NodeGraph;

class Lol : public Lel { public: int X; };

static_assert(sizeof(Lol) == 4);

template<typename T>
class Parent {
private:
  T *Parent;

public:
  T *getParent() const { return Parent; }

};

template<typename Inheritor,
         bool HasParent=true,
         typename NeighborContainer = std::vector<Inheritor *>>
class BidirectionalNode
    : public std::conditional_t<HasParent,
                                Parent<NodeGraph<BidirectionalNode<Inheritor,
                                                                   HasParent,
                                                                   NeighborContainer>>>,
                                Lel> {
public:
  using child_iterator = typename NeighborContainer::iterator;
  using const_child_iterator = typename NeighborContainer::const_iterator;

public:
  void addSuccessor(Inheritor *NewSuccessor) {
    Successors.push_back(NewSuccessor);
    NewSuccessor->Predecessors.push_back(static_cast<Inheritor *>(this));
  }

  auto successors() const {
    return llvm::make_range(Successors.begin(), Successors.end());
  }

  auto successors() {
    return llvm::make_range(Successors.begin(), Successors.end());
  }

  auto predecessors() const {
    return llvm::make_range(Predecessors.begin(), Predecessors.end());
  }

  auto predecessors() {
    return llvm::make_range(Predecessors.begin(), Predecessors.end());
  }

private:
  NeighborContainer Predecessors;
  NeighborContainer Successors;

};

template<typename Node,
         template<typename...> class NodesContainer>
class NodeGraph {
private:
  NodesContainer<std::unique_ptr<Node>> Nodes;

public:
  template<class... Args>
  Node *addNode(Args &&... A) {
    Nodes.push_back(std::make_unique<Node>(std::forward<Args>(A)...));
    return Nodes.back().get();
  }
};

struct MyForwardNode : public ForwardNode<MyForwardNode> {
  MyForwardNode(int) {}
  int m;
};

static_assert(std::is_base_of_v<ForwardNode<MyForwardNode>, MyForwardNode>);
static_assert(
  std::is_base_of_v<const ForwardNode<MyForwardNode>, const MyForwardNode>);

struct MyBidirectionalNode : public BidirectionalNode<MyBidirectionalNode> {
  int m;
};

#include "llvm/ADT/GraphTraits.h"

namespace llvm {

template<typename T>
struct GraphTraits<T *,
  std::enable_if_t<std::is_base_of_v<ForwardNode<std::remove_cv_t<T>>,
                                     std::remove_cv_t<T>>
                   || std::is_base_of_v<BidirectionalNode<std::remove_cv_t<T>>,
                                        std::remove_cv_t<T>>>> {
public:
  using NodeRef = T *;
  using ChildIteratorType = std::conditional_t<std::is_const_v<T>,
                                               typename T::const_child_iterator,
                                               typename T::child_iterator>;

public:
  static ChildIteratorType child_begin(NodeRef N) {
    return N->successors().begin();
  }

  static ChildIteratorType child_end(NodeRef N) {
    return N->successors().end();
  }

  static NodeRef getEntryNode(NodeRef N) { return N; };
};

template<typename T>
struct GraphTraits<
  llvm::Inverse<T *>,
  std::enable_if_t<std::is_base_of_v<BidirectionalNode<std::remove_cv_t<T>>,
                                     std::remove_cv_t<T>>>> {
public:
  using NodeRef = T *;
  using ChildIteratorType = std::conditional_t<std::is_const_v<T>,
                                               typename T::const_child_iterator,
                                               typename T::child_iterator>;

public:
  static ChildIteratorType child_begin(NodeRef N) {
    return N->predecessors().begin();
  }

  static ChildIteratorType child_end(NodeRef N) {
    return N->predecessors().end();
  }

  static NodeRef getEntryNode(NodeRef N) { return N; };
};

} // namespace llvm

NodeGraph<MyForwardNode> X;
NodeGraph<MyBidirectionalNode> X2;

inline void asd() {
  X.addNode(3);
  llvm::GraphTraits<MyForwardNode *>::child_begin(X.addNode(3));
  llvm::GraphTraits<const MyForwardNode *>::child_begin(X.addNode(3));
  llvm::GraphTraits<MyBidirectionalNode *>::child_begin(X2.addNode(3));
  llvm::GraphTraits<const MyBidirectionalNode *>::child_begin(X2.addNode(3));
  llvm::GraphTraits<llvm::Inverse<MyBidirectionalNode *>>::child_begin(
    X2.addNode(3));
  llvm::GraphTraits<llvm::Inverse<const MyBidirectionalNode *>>::child_begin(
    X2.addNode(3));
}

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
