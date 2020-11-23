/// \file AdvancedValueInfo.cpp
/// \brief Test the AdvancedValueInfo analysis

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#define BOOST_TEST_MODULE AdvancedValueInfo
bool init_unit_test();
#include "boost/test/unit_test.hpp"

#include "llvm/Analysis/Passes.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"

#include "revng/BasicAnalyses/AdvancedValueInfo.h"
#include "revng/Support/Debug.h"
#include "revng/Support/IRHelpers.h"
#include "revng/UnitTestHelpers/LLVMTestHelpers.h"
#include "revng/UnitTestHelpers/UnitTestHelpers.h"

using namespace llvm;

class MockupMemoryOracle {
private:
  const llvm::DataLayout &DL;

public:
  MockupMemoryOracle(const llvm::DataLayout &DL) : DL(DL) {}

  const llvm::DataLayout &getDataLayout() const { return DL; }

  MaterializedValue load(Constant *Address) {
    auto *PointerTy = Address->getType()->getPointerElementType();
    unsigned BitWidth = PointerTy->getScalarSizeInBits();
    if (auto *CI = dyn_cast<ConstantInt>(skipCasts(Address)))
      if (getLimitedValue(CI) == 1000)
        return { "symbol", APInt(BitWidth, 0) };
    return { APInt(BitWidth, 42) };
  }
};

class TestAdvancedValueInfoPass : public ModulePass {
public:
  using ResultsMap = std::map<Value *, MaterializedValues>;

public:
  static char ID;

public:
  TestAdvancedValueInfoPass() : ModulePass(ID), Results(nullptr) {}
  TestAdvancedValueInfoPass(ResultsMap &Results) :
    ModulePass(ID), Results(&Results) {}

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LazyValueInfoWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
  }

  bool runOnModule(llvm::Module &M) override;

private:
  ResultsMap *Results;
};

char TestAdvancedValueInfoPass::ID = 0;

#define PASS_FLAG "test-advanced-value-info"
#define PASS_DESCRIPTION "Test Pass for the Advanced Value Info analysis"

using Register = RegisterPass<TestAdvancedValueInfoPass>;
static Register Y(PASS_FLAG, PASS_DESCRIPTION, false, false);

#undef PASS_FLAG
#undef PASS_DESCRIPTION

bool TestAdvancedValueInfoPass::runOnModule(llvm::Module &M) {
  Function &Root = *M.getFunction("main");
  auto &LVI = getAnalysis<LazyValueInfoWrapperPass>(Root).getLVI();
  auto &DT = getAnalysis<DominatorTreeWrapperPass>(Root).getDomTree();
  auto &SCEV = getAnalysis<ScalarEvolutionWrapperPass>(Root).getSE();

  MockupMemoryOracle MO(M.getDataLayout());
  AdvancedValueInfo<MockupMemoryOracle> AVI(LVI, SCEV, DT, MO);

  for (User *U : M.getGlobalVariable("pc", true)->users()) {
    if (auto *Store = dyn_cast<StoreInst>(U)) {
      Value *V = Store->getValueOperand();
      (*Results)[V] = AVI.explore(Store->getParent(), V);
    }
  }

  return false;
}

using CheckMap = std::map<const char *, MaterializedValues>;

static void checkAdvancedValueInfo(const char *Body, const CheckMap &Map) {
  auto &Registry = *PassRegistry::getPassRegistry();
  initializeDominatorTreeWrapperPassPass(Registry);
  initializeLazyValueInfoWrapperPassPass(Registry);

  LLVMContext C;
  std::unique_ptr<llvm::Module> M = loadModule(C, Body);
  revng_check(not verifyModule(*M, &dbgs()));

  Function *F = M->getFunction("main");

  TestAdvancedValueInfoPass::ResultsMap Results;

  legacy::PassManager PM;
  PM.add(createLazyValueInfoPass());
  PM.add(new ScalarEvolutionWrapperPass);
  PM.add(new TestAdvancedValueInfoPass(Results));
  PM.run(*M);

  TestAdvancedValueInfoPass::ResultsMap Reference;
  for (auto &P : Map)
    Reference[instructionByName(F, P.first)] = P.second;

  revng_check(Results == Reference);
}

static APInt AI64(uint64_t Value) {
  return APInt(64, Value);
}

BOOST_AUTO_TEST_CASE(TestConstant) {

  checkAdvancedValueInfo(R"LLVM(
  %constant = add i64 4194424, 0
  store i64 %constant, i64* @pc
  unreachable
)LLVM",
                         { { "constant", { AI64(4194424) } } });

  checkAdvancedValueInfo(R"LLVM(
  %other = add i64 4194424, 0
  %constant = add i64 %other, 0
  store i64 %constant, i64* @pc
  unreachable
)LLVM",
                         { { "constant", { AI64(4194424) } } });
}

BOOST_AUTO_TEST_CASE(TestRange) {
  checkAdvancedValueInfo(R"LLVM(
  %to_store = load i64, i64 *@pc
  %cmp = icmp ult i64 %to_store, 5
  br i1 %cmp, label %smaller, label %end

smaller:
  store i64 %to_store, i64* @pc
  br label %end

end:
  unreachable

)LLVM",
                         { { "to_store",
                             { AI64(0),
                               AI64(1),
                               AI64(2),
                               AI64(3),
                               AI64(4) } } });

  checkAdvancedValueInfo(R"LLVM(
  %original = load i64, i64 *@pc
  %cmp = icmp ult i64 %original, 5
  br i1 %cmp, label %smaller, label %end

smaller:
  %shifted = shl i64 %original, 1
  store i64 %shifted, i64* @pc
  br label %end

end:
  unreachable

)LLVM",
                         { { "shifted",
                             { AI64(0),
                               AI64(2),
                               AI64(4),
                               AI64(6),
                               AI64(8) } } });
}

BOOST_AUTO_TEST_CASE(TestPhi) {
  checkAdvancedValueInfo(R"LLVM(
  br label %start

start:
  br label %use_phi

use_phi:
  %to_store = phi i64 [ 5, %start ]
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { AI64(5) } } });

  checkAdvancedValueInfo(R"LLVM(
  br label %start

start:
  %pre_phi = add i64 5, 0
  br label %use_phi

use_phi:
  %to_store = phi i64 [ %pre_phi, %start ]
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { AI64(5) } } });

  // Two distinct constants
  checkAdvancedValueInfo(R"LLVM(
  br label %start

start:
  br i1 true, label %true, label %false

true:
  %pre_phi1 = zext i32 5 to i64
  br label %use_phi

false:
  %pre_phi2 = zext i32 10 to i64
  br label %use_phi

use_phi:
  ; Here LVI will tell us that to_store is in [5, 10], but we want to be more
  ; accurate than that
  %to_store = phi i64 [ %pre_phi1, %true ], [ %pre_phi2, %false ]
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { AI64(5), AI64(10) } } });

  // Multi-level phi
  checkAdvancedValueInfo(R"LLVM(
  br i1 true, label %true, label %false

true:
  br i1 true, label %true_true, label %true_false

false:
  br i1 true, label %false_true, label %false_false

true_true:
  %five = add i64 0, 5
  br label %true_merge

true_false:
  %ten = add i64 0, 10
  br label %true_merge

true_merge:
   %true_phi = phi i64 [ %five, %true_true ], [ %ten, %true_false ]
  br label %use_phi

false_true:
  %nineteen = add i64 0, 19
  br label %false_merge

false_false:
  %twentytwo = add i64 0, 22
  br label %false_merge

false_merge:
  %false_phi = phi i64 [ %nineteen, %false_true ], [ %twentytwo, %false_false ]
  br label %use_phi

use_phi:
  %to_store = phi i64 [ %true_phi, %true_merge ], [ %false_phi, %false_merge ]
  store i64 %to_store, i64* @pc
  ret void

)LLVM",
                         { { "to_store",
                             { AI64(5), AI64(10), AI64(19), AI64(22) } } });

  // Two disjoint ranges and a constant
  checkAdvancedValueInfo(R"LLVM(
  br label %entry

entry:
  %x = load i64, i64* @rax
  %equal100 = icmp ne i64 %x, 100
  br i1 %equal100, label %true, label %final

true:
  %zerofive_condition = icmp ult i64 %x, 5
  br i1 %zerofive_condition, label %true_merge, label %continue

continue:
  %gt10 = icmp ugt i64 %x, 10
  %lt15 = icmp ult i64 %x, 15
  %in10_15 = and i1 %gt10, %lt15
  br i1 %in10_15, label %true_merge, label %dead

dead:
  unreachable

true_merge:
  %true_result = phi i64 [ %x, %true ], [ %x, %continue ]
  br label %final

final:
  %to_store = phi i64 [ %x, %entry ], [ %true_result, %true_merge ]
  store i64 %to_store, i64* @pc
  ret void

)LLVM",
                         { { "to_store",
                             { AI64(0),
                               AI64(1),
                               AI64(2),
                               AI64(3),
                               AI64(4),
                               AI64(11),
                               AI64(12),
                               AI64(13),
                               AI64(14),
                               AI64(100) } } });
}

BOOST_AUTO_TEST_CASE(TestLoops) {
  checkAdvancedValueInfo(R"LLVM(
  br label %entry

entry:
  %initial = add i64 5, 0
  br label %start

start:
  %to_store = phi i64 [ %initial, %entry ], [ %in_loop, %start ]
  store i64 %to_store, i64* @pc
  %in_loop = add i64 8, 0
  br i1 false, label %end, label %start

end:
  unreachable

)LLVM",
                         { { "to_store", { AI64(5), AI64(8) } } });

  // Note: LazyValueInfo is not expressive enough to track the fact that the add
  //       is monotone. This is test is to ensure we don't end in an infinite
  //       loop in presence of a phi in a loop.
  checkAdvancedValueInfo(R"LLVM(
  br label %entry

entry:
  %initial = add i64 5, 0
  br label %start

start:
  %to_store = phi i64 [ %initial, %entry ], [ %in_loop, %start ]
  store i64 %to_store, i64* @pc
  %in_loop = add i64 %to_store, 1
  %condition = icmp ugt i64 %in_loop, 10
  br i1 %condition, label %end, label %start

end:
  unreachable

)LLVM",
                         { { "to_store",
                             { AI64(0),
                               AI64(1),
                               AI64(2),
                               AI64(3),
                               AI64(4),
                               AI64(5),
                               AI64(6),
                               AI64(7),
                               AI64(8),
                               AI64(9) } } });
}

BOOST_AUTO_TEST_CASE(TestMemory) {
  checkAdvancedValueInfo(R"LLVM(
  %fortytwo = load i64, i64* inttoptr (i64 4294967296 to i64*)
  %to_store = add i64 %fortytwo, 1
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { AI64(43) } } });
}

BOOST_AUTO_TEST_CASE(TestBswap) {
  checkAdvancedValueInfo(R"LLVM(
  %to_store = call i64 @llvm.bswap.i64(i64 255)
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { AI64(0xFFULL << (7 * 8)) } } });
}

BOOST_AUTO_TEST_CASE(TestSymbol) {
  checkAdvancedValueInfo(R"LLVM(
  %symbol = load i64, i64* inttoptr (i64 1000 to i64*)
  %to_store = add i64 %symbol, 10
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", { { "symbol", AI64(10) } } } });

  // We don't handle multiplication of symbol values
  checkAdvancedValueInfo(R"LLVM(
  %symbol = load i64, i64* inttoptr (i64 1000 to i64*)
  %to_store = mul i64 %symbol, 10
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store", {} } });
}

BOOST_AUTO_TEST_CASE(TestDisjoint) {
  // Two disjoint intervals without phis
  checkAdvancedValueInfo(R"LLVM(
  br label %start

start:
  %to_store = load i64, i64* @rax
  %gt10 = icmp ugt i64 %to_store, 10
  %lt15 = icmp ult i64 %to_store, 15
  %in10_15 = and i1 %gt10, %lt15
  br i1 %in10_15, label %end, label %false

false:
  %gt30 = icmp ugt i64 %to_store, 30
  %lt35 = icmp ult i64 %to_store, 35
  %in30_35 = and i1 %gt30, %lt35
  br i1 %in30_35, label %end, label %exit

exit:
  unreachable

end:
  store i64 %to_store, i64* @pc
  unreachable

)LLVM",
                         { { "to_store",
                             { AI64(11),
                               AI64(12),
                               AI64(13),
                               AI64(14),
                               AI64(31),
                               AI64(32),
                               AI64(33),
                               AI64(34) } } });
}
