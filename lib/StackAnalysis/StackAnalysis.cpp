/// \file StackAnalysis.cpp
/// \brief Implementation of the stack analysis, which provides information
///        about function boundaries, basic block types, arguments and return
///        values.

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <fstream>
#include <map>
#include <sstream>
#include <vector>

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "revng/BasicAnalyses/GeneratedCodeBasicInfo.h"
#include "revng/Model/Binary.h"
#include "revng/StackAnalysis/StackAnalysis.h"
#include "revng/Support/CommandLine.h"
#include "revng/Support/IRHelpers.h"
#include "revng/Support/MetadataOutput.h"

#include "Cache.h"
#include "InterproceduralAnalysis.h"
#include "Intraprocedural.h"

using llvm::BasicBlock;
using llvm::Function;
using llvm::Module;
using llvm::RegisterPass;

static Logger<> ClobberedLog("clobbered");
static Logger<> StackAnalysisLog("stackanalysis");
static Logger<> CFEPLog("cfep");

using namespace llvm::cl;

namespace StackAnalysis {

const std::set<llvm::GlobalVariable *> EmptyCSVSet;

template<>
char StackAnalysis<true>::ID = 0;

namespace {
const char *Name = "Stack Analysis Pass";
static RegisterPass<StackAnalysis<false>> X("stack-analysis", Name, true, true);

static opt<std::string> StackAnalysisOutputPath("stack-analysis-output",
                                                desc("Destination path for the "
                                                     "Static Analysis Pass"),
                                                value_desc("path"),
                                                cat(MainCategory));

} // namespace

template<typename T>
static void benchmark(T Function) {
  for (unsigned I = 0; I < 10; I++)
    Function();

  typedef std::chrono::high_resolution_clock Clock;
  auto t1 = Clock::now();
  for (unsigned I = 0; I < 100; I++)
    Function();
  auto t2 = Clock::now();
  llvm::outs() << (t2 - t1).count() << '\n';
}

template<>
char StackAnalysis<false>::ID = 0;

using RegisterABI = RegisterPass<StackAnalysis<true>>;
static RegisterABI Y("abi-analysis", "ABI Analysis Pass", true, true);

static opt<std::string> ABIAnalysisOutputPath("abi-analysis-output",
                                              desc("Destination path for the "
                                                   "ABI Analysis Pass"),
                                              value_desc("path"),
                                              cat(MainCategory));

class BasicBlockVisitHelper
  : public llvm::df_iterator_default_set<BasicBlock *> {
public:
  using Base = df_iterator_default_set<BasicBlock *>;
  using Inserter = typename SortedVector<model::BasicBlock>::BatchInserter;

private:
  std::stack<model::BasicBlock> BasicBlocksStack;
  Inserter &I;
  const std::map<llvm::BasicBlock *, BranchType::Values> &Allowed;

public:
  BasicBlockVisitHelper(
    Inserter &I,
    const std::map<llvm::BasicBlock *, BranchType::Values> &Allowed) :
    I(I), Allowed(Allowed) {}

public:
  std::pair<iterator, bool> insert(BasicBlock *BB) {
    if (Allowed.count(BB) == 0)
      return { begin(), false };

    auto Result = Base::insert(BB);
    if (Result.second and GeneratedCodeBasicInfo::isJumpTarget(BB)) {
      auto MA = getBasicBlockPC(BB);
      dbg << "Entering ";
      MA.dump(dbg);
      dbg << "\n";
      BasicBlocksStack.emplace(MA, MetaAddress::invalid());
    }
    return Result;
  }

  void completed(BasicBlock *BB) {
    if (GeneratedCodeBasicInfo::isJumpTarget(BB)) {
      auto MA = getBasicBlockPC(BB);
      dbg << "Leaving ";
      MA.dump(dbg);
      dbg << "\n";
      revng_assert(BasicBlocksStack.top().Start == MA);
      I.insert(BasicBlocksStack.top());
      BasicBlocksStack.pop();
    }
    Base::completed(BB);
  }

public:
  model::BasicBlock &currentBlock() { return BasicBlocksStack.top(); }
};

static void commitToModel(GeneratedCodeBasicInfo &GCBI,
                          Function *F,
                          const FunctionsSummary &Summary,
                          model::Binary &TheBinary) {
  using namespace model;

  std::map<llvm::BasicBlock *, MetaAddress> GeneratingJumpTarget;
  {
    llvm::DominatorTree DT(*F);
    for (llvm::BasicBlock &BB : *F) {
      if (not GeneratedCodeBasicInfo::isTranslated(&BB)
          and GCBI.getType(&BB)
                != BlockType::IndirectBranchDispatcherHelperBlock)
        continue;

      auto *DTNode = DT.getNode(&BB);
      revng_assert(DTNode != nullptr);

      while (not GeneratedCodeBasicInfo::isJumpTarget(DTNode->getBlock())) {
        DTNode = DTNode->getIDom();
        revng_assert(DTNode != nullptr);
      }

      GeneratingJumpTarget[&BB] = getBasicBlockPC(DTNode->getBlock());
    }
  }

  for (const auto &[Entry, FunctionSummary] : Summary.Functions) {
    if (Entry == nullptr)
      continue;

    //
    // Initialize model::Function
    //

    // Get the entry point address
    MetaAddress EntryPC = getBasicBlockPC(Entry);
    revng_assert(EntryPC.isValid());

    // Create the function
    revng_assert(TheBinary.Functions.count(EntryPC) == 0);
    model::Function &Function = TheBinary.Functions[EntryPC];

    // Assign a name
    Function.Name = Entry->getName();

    using FT = model::FunctionType::Values;
    Function.Type = static_cast<FT>(FunctionSummary.Type);

    // auto Inserter = Function.CFG.batch_insert();
    // BasicBlockVisitHelper VisitHelper(Inserter, FunctionSummary.BasicBlocks);
    for (auto &[BB, Branch] : FunctionSummary.BasicBlocks) {
      // Remap BranchType to FunctionEdgeType
      namespace FET = FunctionEdgeType;
      FET::Values EdgeType = FET::Invalid;

      switch (Branch) {
      case BranchType::Invalid:
      case BranchType::FakeFunction:
      case BranchType::RegularFunction:
      case BranchType::NoReturnFunction:
      case BranchType::UnhandledCall:
        revng_abort();
        break;

      case BranchType::InstructionLocalCFG:
        EdgeType = FET::Invalid;
        break;

      case BranchType::FunctionLocalCFG:
        EdgeType = FET::DirectBranch;
        break;

      case BranchType::FakeFunctionCall:
        EdgeType = FET::FakeFunctionCall;
        break;

      case BranchType::FakeFunctionReturn:
        EdgeType = FET::FakeFunctionReturn;
        break;

      case BranchType::HandledCall:
        EdgeType = FET::FunctionCall;
        break;

      case BranchType::IndirectCall:
        EdgeType = FET::IndirectCall;
        break;

      case BranchType::Return:
        EdgeType = FET::Return;
        break;

      case BranchType::BrokenReturn:
        EdgeType = FET::BrokenReturn;
        break;

      case BranchType::IndirectTailCall:
        EdgeType = FET::IndirectTailCall;
        break;

      case BranchType::LongJmp:
        EdgeType = FET::LongJmp;
        break;

      case BranchType::Killer:
        EdgeType = FET::Killer;
        break;

      case BranchType::Unreachable:
        EdgeType = FET::Unreachable;
        break;
      }

      if (EdgeType == FET::Invalid)
        continue;

      // Identify Source address
      auto [Source, Size] = getPC(BB->getTerminator());
      Source += Size;
      revng_assert(Source.isValid());

      // Identify Destination address
      MetaAddress JumpTargetAddress = GeneratingJumpTarget.at(BB);
      model::BasicBlock &CurrentBlock = Function
                                          .CFG[{ JumpTargetAddress, Source }];

      if (EdgeType == FET::DirectBranch) {
        auto Successors = GCBI.getSuccessors(BB);
        for (const MetaAddress &Destination : Successors.Addresses) {
          llvm::errs() << "From " << Source.toString() << " (" << getName(BB)
                       << ")"
                       << " to " << Destination.toString() << " of type "
                       << FunctionEdgeType::getName(EdgeType) << "\n";
          CurrentBlock.Successors.insert(FunctionEdge{ Destination, EdgeType });
        }
      } else if (EdgeType == FET::FakeFunctionReturn) {
        auto [First, Last] = FunctionSummary.FakeReturns.equal_range(BB);
        revng_assert(First != Last);
        for (const auto &[_, Destination] : make_range(First, Last)) {
          llvm::errs() << "From " << Source.toString() << " (" << getName(BB)
                       << ")"
                       << " to " << Destination.toString() << " of type "
                       << FunctionEdgeType::getName(EdgeType) << "\n";
          CurrentBlock.Successors.insert(FunctionEdge{ Destination, EdgeType });
        }
      } else {
        llvm::BasicBlock *Successor = BB->getSingleSuccessor();
        MetaAddress Destination = MetaAddress::invalid();
        if (Successor != nullptr)
          Destination = getBasicBlockPC(Successor);

        llvm::errs() << "From " << Source.toString() << " (" << getName(BB)
                     << ")"
                     << " to " << Destination.toString() << " ("
                     << getName(Successor) << ")"
                     << " of type " << FunctionEdgeType::getName(EdgeType)
                     << "\n";

        // Record the edge in the CFG
        CurrentBlock.Successors.insert(FunctionEdge{ Destination, EdgeType });
      }
    }
    // Inserter.commit();

#if 0
    for (const auto &[Block, Branch] : FunctionSummary.BasicBlocks) {
      // Remap BranchType to FunctionEdgeType
      namespace FET = FunctionEdgeType;
      FET::Values EdgeType = FET::Invalid;

      switch (Branch) {
      case BranchType::Invalid:
      case BranchType::FakeFunction:
      case BranchType::RegularFunction:
      case BranchType::NoReturnFunction:
      case BranchType::UnhandledCall:
        revng_abort();
        break;

      case BranchType::InstructionLocalCFG:
        EdgeType = FET::Invalid;
        break;

      case BranchType::FunctionLocalCFG:
        EdgeType = FET::DirectBranch;
        break;

      case BranchType::FakeFunctionCall:
        EdgeType = FET::FakeFunctionCall;
        break;

      case BranchType::FakeFunctionReturn:
        EdgeType = FET::FakeFunctionReturn;
        break;

      case BranchType::HandledCall:
        EdgeType = FET::FunctionCall;
        break;

      case BranchType::IndirectCall:
        EdgeType = FET::IndirectCall;
        break;

      case BranchType::Return:
        EdgeType = FET::Return;
        break;

      case BranchType::BrokenReturn:
        EdgeType = FET::BrokenReturn;
        break;

      case BranchType::IndirectTailCall:
        EdgeType = FET::IndirectTailCall;
        break;

      case BranchType::LongJmp:
        EdgeType = FET::LongJmp;
        break;

      case BranchType::Killer:
        EdgeType = FET::Killer;
        break;

      case BranchType::Unreachable:
        EdgeType = FET::Unreachable;
        break;
      }

      if (EdgeType == FET::Invalid)
        continue;

      // Identify Source address
      auto [Source, Size] = getPC(Block->getTerminator());
      Source += Size;
      revng_assert(Source.isValid());

      // Identify Destination address
      MetaAddress Destination = MetaAddress::invalid();
      llvm::BasicBlock *Successor = Block->getSingleSuccessor();
      if (Successor != nullptr)
        Destination = getBasicBlockPC(Successor);

      llvm::errs() << "From " << Source.toString() << " (" << getName(Block)
                   << ")"
                   << " to " << Destination.toString() << " ("
                   << getName(Successor) << ")"
                   << " of type " << FunctionEdgeType::getName(EdgeType)
                   << "\n";

      // Record the edge in the CFG
      FunctionEdge NewEdge{ Source, Destination, EdgeType };
      if (Function.CFG.count(NewEdge) == 0)
        Function.CFG.insert(NewEdge);
    }
#endif

    revng_check(Function.verifyCFG());
  }
}

template<bool AnalyzeABI>
bool StackAnalysis<AnalyzeABI>::runOnModule(Module &M) {
  Function &F = *M.getFunction("root");

  revng_log(PassesLog, "Starting StackAnalysis");

  auto &GCBI = getAnalysis<GeneratedCodeBasicInfo>();

  auto &LMP = getAnalysis<LoadModelPass>();

  // The stack analysis works function-wise. We consider two sets of functions:
  // first (Force == true) those that are highly likely to be real functions
  // (i.e., they have a direct call) and then (Force == false) all the remaining
  // candidates whose entry point is not included in any function of the first
  // set.

  struct CFEP {
    CFEP(BasicBlock *Entry, bool Force) : Entry(Entry), Force(Force) {}

    BasicBlock *Entry;
    bool Force;
  };
  std::vector<CFEP> Functions;

  // Register all the Candidate Function Entry Points
  for (BasicBlock &BB : F) {

    if (GCBI.getType(&BB) != BlockType::JumpTargetBlock)
      continue;

    uint32_t Reasons = GCBI.getJTReasons(&BB);
    bool IsFunctionSymbol = hasReason(Reasons, JTReason::FunctionSymbol);
    bool IsCallee = hasReason(Reasons, JTReason::Callee);
    bool IsUnusedGlobalData = hasReason(Reasons, JTReason::UnusedGlobalData);
    bool IsMemoryStore = hasReason(Reasons, JTReason::MemoryStore);
    bool IsPCStore = hasReason(Reasons, JTReason::PCStore);
    bool IsReturnAddress = hasReason(Reasons, JTReason::ReturnAddress);
    bool IsLoadAddress = hasReason(Reasons, JTReason::LoadAddress);

    if (IsFunctionSymbol or IsCallee) {
      // Called addresses are a strong hint
      Functions.emplace_back(&BB, true);
    } else if (not IsLoadAddress
               and (IsUnusedGlobalData
                    || (IsMemoryStore and not IsPCStore
                        and not IsReturnAddress))) {
      // TODO: keep IsReturnAddress?
      // Consider addresses found in global data that have not been used or
      // addresses that are not return addresses and do not end up in the PC
      // directly.
      Functions.emplace_back(&BB, false);
    }
  }

  for (CFEP &Function : Functions) {
    revng_log(CFEPLog,
              getName(Function.Entry) << (Function.Force ? " (forced)" : ""));
  }

  // Initialize the cache where all the results will be accumulated
  Cache TheCache(&F, &GCBI);

  // Pool where the final results will be collected
  ResultsPool Results;

  // First analyze all the `Force`d functions (i.e., with an explicit direct
  // call)
  for (CFEP &Function : Functions) {
    if (Function.Force) {
      auto &GCBI = getAnalysis<GeneratedCodeBasicInfo>();
      InterproceduralAnalysis SA(TheCache, GCBI, AnalyzeABI);
      SA.run(Function.Entry, Results);
    }
  }

  // Now analyze all the remaining candidates which are not already part of
  // another function
  std::set<BasicBlock *> Visited = Results.visitedBlocks();
  for (CFEP &Function : Functions) {
    if (not Function.Force and Visited.count(Function.Entry) == 0) {
      auto &GCBI = getAnalysis<GeneratedCodeBasicInfo>();
      InterproceduralAnalysis SA(TheCache, GCBI, AnalyzeABI);
      SA.run(Function.Entry, Results);
    }
  }

  for (CFEP &Function : Functions) {
    using IFS = IntraproceduralFunctionSummary;
    BasicBlock *Entry = Function.Entry;
    llvm::Optional<const IFS *> Cached = TheCache.get(Entry);
    revng_assert(Cached or TheCache.isFakeFunction(Entry));

    // Has this function been analyzed already? If so, only now we register it
    // in the ResultsPool.
    FunctionType::Values Type;
    if (TheCache.isFakeFunction(Entry))
      Type = FunctionType::Fake;
    else if (TheCache.isNoReturnFunction(Entry))
      Type = FunctionType::NoReturn;
    else
      Type = FunctionType::Regular;

    // Regular functions need to be composed by at least a basic block
    if (Cached) {
      const IFS *Summary = *Cached;
      if (Type == FunctionType::Regular)
        revng_assert(Summary->BranchesType.size() != 0);

      Results.registerFunction(Entry, Type, Summary);
    } else {
      Results.registerFunction(Entry, Type, nullptr);
    }
  }

  GrandResult = Results.finalize(&M, &TheCache);

  if (ClobberedLog.isEnabled()) {
    for (auto &P : GrandResult.Functions) {
      ClobberedLog << getName(P.first) << ":";
      for (const llvm::GlobalVariable *CSV : P.second.ClobberedRegisters)
        ClobberedLog << " " << CSV->getName().data();
      ClobberedLog << DoLog;
    }
  }

  if (StackAnalysisLog.isEnabled()) {
    std::stringstream Output;
    GrandResult.dump(&M, Output);
    TextRepresentation = Output.str();
    revng_log(StackAnalysisLog, TextRepresentation);
  }

  revng_log(PassesLog, "Ending StackAnalysis");

  if (AnalyzeABI and ABIAnalysisOutputPath.getNumOccurrences() == 1) {
    std::ofstream Output;
    serialize(pathToStream(ABIAnalysisOutputPath, Output));
  } else if (not AnalyzeABI
             and StackAnalysisOutputPath.getNumOccurrences() == 1) {
    std::ofstream Output;
    serialize(pathToStream(StackAnalysisOutputPath, Output));
  }

  commitToModel(GCBI, &F, GrandResult, LMP.getWriteableModel());

  return false;
}

template<bool AnalyzeABI>
void StackAnalysis<AnalyzeABI>::serializeMetadata(Function &F) {
  using namespace llvm;

  const FunctionsSummary &Summary = GrandResult;

  LLVMContext &Context = getContext(&F);
  QuickMetadata QMD(Context);

  // Temporary data structure so we can set all the `revng.func.member.of` in a
  // single shot at the end
  std::map<Instruction *, std::vector<Metadata *>> MemberOf;

  auto &GCBI = getAnalysis<GeneratedCodeBasicInfo>();

  // Loop over all the detected functions
  for (const auto &P : Summary.Functions) {
    BasicBlock *Entry = P.first;
    const FunctionsSummary::FunctionDescription &Function = P.second;

    if (Entry == nullptr or Function.BasicBlocks.size() == 0)
      continue;

    MetaAddress EntryPC = getBasicBlockPC(Entry);

    //
    // Add `revng.func.entry`:
    // {
    //   name,
    //   address,
    //   type,
    //   { clobbered csv, ... },
    //   { { csv, argument, return value }, ... }
    // }
    //
    auto TypeMD = QMD.get(FunctionType::getName(Function.Type));

    // Clobbered registers metadata
    std::vector<Metadata *> ClobberedMDs;
    for (GlobalVariable *ClobberedCSV : Function.ClobberedRegisters) {
      if (not GCBI.isServiceRegister(ClobberedCSV))
        ClobberedMDs.push_back(QMD.get(ClobberedCSV));
    }

    // Register slots metadata
    std::vector<Metadata *> SlotMDs;
    if (AnalyzeABI) {
      for (auto &P : Function.RegisterSlots) {
        if (GCBI.isServiceRegister(P.first))
          continue;

        auto *CSV = QMD.get(P.first);
        auto *Argument = QMD.get(P.second.Argument.valueName());
        auto *ReturnValue = QMD.get(P.second.ReturnValue.valueName());
        SlotMDs.push_back(QMD.tuple({ CSV, Argument, ReturnValue }));
      }
    }

    // Create revng.func.entry metadata
    MDTuple *FunctionMD = QMD.tuple({ QMD.get(getName(Entry)),
                                      QMD.get(GCBI.toConstant(EntryPC)),
                                      TypeMD,
                                      QMD.tuple(ClobberedMDs),
                                      QMD.tuple(SlotMDs) });
    Entry->getTerminator()->setMetadata("revng.func.entry", FunctionMD);

    if (AnalyzeABI) {
      //
      // Create func.call
      //
      for (const FunctionsSummary::CallSiteDescription &CallSite :
           Function.CallSites) {
        Instruction *Call = CallSite.Call;

        // Register slots metadata
        std::vector<Metadata *> SlotMDs;
        for (auto &P : CallSite.RegisterSlots) {
          if (GCBI.isServiceRegister(P.first))
            continue;

          auto *CSV = QMD.get(P.first);
          auto *Argument = QMD.get(P.second.Argument.valueName());
          auto *ReturnValue = QMD.get(P.second.ReturnValue.valueName());
          SlotMDs.push_back(QMD.tuple({ CSV, Argument, ReturnValue }));
        }

        Call->setMetadata("func.call", QMD.tuple(QMD.tuple(SlotMDs)));
      }
    }

    //
    // Create revng.func.member.of
    //

    // Loop over all the basic blocks composing the function
    for (const auto &P : Function.BasicBlocks) {
      BasicBlock *BB = P.first;
      BranchType::Values Type = P.second;

      auto *Pair = QMD.tuple({ FunctionMD, QMD.get(getName(Type)) });

      // Register that this block is associated to this function
      MemberOf[BB->getTerminator()].push_back(Pair);
    }
  }

  // Apply `revng.func.member.of`
  for (auto &P : MemberOf)
    P.first->setMetadata("revng.func.member.of", QMD.tuple(P.second));
}

template void StackAnalysis<true>::serializeMetadata(Function &F);
template void StackAnalysis<false>::serializeMetadata(Function &F);

} // namespace StackAnalysis
