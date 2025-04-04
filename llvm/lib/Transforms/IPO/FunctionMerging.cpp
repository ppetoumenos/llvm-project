//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the general function merging optimization.
//
// It identifies similarities between functions, and If profitable, merges them
// into a single function, replacing the original ones. Functions do not need
// to be identical to be merged. In fact, there is very little restriction to
// merge two function, however, the produced merged function can be larger than
// the two original functions together. For that reason, it uses the
// TargetTransformInfo analysis to estimate the code-size costs of instructions
// in order to estimate the profitability of merging two functions.
//
// This function merging transformation has three major parts:
// 1. The input functions are linearized, representing their CFGs as sequences
//    of labels and instructions.
// 2. We apply a sequence alignment algorithm, namely, the Needleman-Wunsch
//    algorithm, to identify similar code between the two linearized functions.
// 3. We use the aligned sequences to perform code generate, producing the new
//    merged function, using an extra parameter to represent the function
//    identifier.
//
// This pass integrates the function merging transformation with an exploration
// framework. For every function, the other functions are ranked based their
// degree of similarity, which is computed from the functions' fingerprints.
// Only the top candidates are analyzed in a greedy manner and if one of them
// produces a profitable result, the merged function is taken.
//
//===----------------------------------------------------------------------===//
//
// This optimization was proposed in
//
// Function Merging by Sequence Alignment (CGO'19)
// Rodrigo C. O. Rocha, Pavlos Petoumenos, Zheng Wang, Murray Cole, Hugh Leather
//
// Effective Function Merging in the SSA Form (PLDI'20)
// Rodrigo C. O. Rocha, Pavlos Petoumenos, Zheng Wang, Murray Cole, Hugh Leather
//
// HyFM: Function Merging for Free (LCTES'21)
// Rodrigo C. O. Rocha, Pavlos Petoumenos, Zheng Wang, Murray Cole, Kim
// Hazelwood, Hugh Leather
//
// F3M: Fast Focused Function Merging (CGO'22)
// Sean Sterling, Rodrigo C. O. Rocha, Hugh Leather, Kim Hazelwood, Michael
// O'Boyle, Pavlos Petoumenos
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO/FunctionMerging.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Support/Error.h"
#include "llvm/Support/Timer.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormatVariadic.h"

#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/IteratedDominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"

#include "llvm/Support/RandomNumberGenerator.h"

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"

#include "llvm/Analysis/Utils/Local.h"
#include "llvm/Transforms/Utils/Local.h"

#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Transforms/IPO.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"

#include "llvm/Analysis/InlineSizeEstimatorAnalysis.h"

#include <algorithm>
#include <array>
#include <fstream>
#include <functional>
#include <queue>
#include <random>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <climits>
#include <cstdlib>
#include <ctime>

#ifdef __unix__
/* __unix__ is usually defined by compilers targeting Unix systems */
#include <unistd.h>
#elif defined(_WIN32) || defined(WIN32)
/* _Win32 is usually defined by compilers targeting 32 or   64 bit Windows
 * systems */
#include <windows.h>
#endif

#define DEBUG_TYPE "func-merging"

#define CHANGES
#define F3M_FIXES

using namespace llvm;

static cl::opt<int> MergingOverheadThreshold(
    "func-merging-threshold", cl::init(0), cl::Hidden,
    cl::desc("Threshold of allowed overhead for merging function"));

static cl::opt<bool> Debug("func-merging-debug", cl::init(false), cl::Hidden,
                           cl::desc("Outputs debug information"));

static cl::opt<bool> TimingDebug("func-merging-timing", cl::init(false),
                                 cl::Hidden,
                                 cl::desc("Outputs timing information"));

static cl::opt<bool> Verbose(
    "func-merging-verbose", cl::init(false), cl::Hidden,
    cl::desc(
        "Outputs detailed information about what function merging is doing"));

static cl::opt<bool>
    EnableOperandReordering("func-merging-operand-reorder", cl::init(false),
                            cl::Hidden, cl::desc("Enable operand reordering"));

static cl::opt<bool>
    HasWholeProgram("func-merging-whole-program", cl::init(false), cl::Hidden,
                    cl::desc("Function merging applied on whole program"));

static cl::opt<bool>
    EnablePA("func-merging-pa", cl::init(false), cl::Hidden,
             cl::desc("Enable Function Merging using Pairwise Alignment"));

static cl::opt<bool> EnableNW(
    "func-merging-nw", cl::init(false), cl::Hidden,
    cl::desc("Enable Function Merging using Needleman-Wunsch Alignment"));

static cl::opt<bool> EnableSALSSACoalescing(
    "func-merging-coalescing", cl::init(true), cl::Hidden,
    cl::desc("Enable phi-node coalescing during SSA reconstruction"));

static cl::opt<bool> ReuseMergedFunctions(
    "func-merging-reuse-merges", cl::init(true), cl::Hidden,
    cl::desc("Try to reuse merged functions for another merge operation"));

static cl::opt<unsigned>
    MaxNumSelection("func-merging-max-selects", cl::init(500), cl::Hidden,
                    cl::desc("Maximum number of allowed operand selection"));

static cl::opt<bool>
    EnableF3M("func-merging-f3m", cl::init(false), cl::Hidden,
              cl::desc("Enable function pairing based on MinHashes and LSH"));

static cl::opt<unsigned>
    LSHRows("hyfm-f3m-rows", cl::init(2), cl::Hidden,
            cl::desc("Number of rows in the LSH structure"));

static cl::opt<unsigned>
    LSHBands("hyfm-f3m-bands", cl::init(100), cl::Hidden,
             cl::desc("Number of bands in the LSH structure"));

static cl::opt<bool> AdaptiveThreshold(
    "adaptive-threshold", cl::init(false), cl::Hidden,
    cl::desc("Adaptively define a new threshold based on the application"));

static cl::opt<bool> AdaptiveBands(
    "adaptive-bands", cl::init(false), cl::Hidden,
    cl::desc("Adaptively define the LSH geometry based on the application"));

static cl::opt<double>
    RankingDistance("ranking-distance", cl::init(1.0), cl::Hidden,
                    cl::desc("Define a threshold to be used"));

static cl::opt<bool>
    ReportStats("func-merging-report", cl::init(false), cl::Hidden,
                cl::desc("Only report the distances and alignment between all "
                         "allowed function pairs"));

static cl::opt<bool> Deterministic(
    "func-merging-deterministic", cl::init(true), cl::Hidden,
    cl::desc("Replace all random number generators with deterministic values"));

static cl::opt<unsigned>
    BucketSizeCap("bucket-size-cap", cl::init(1000000000), cl::Hidden,
                  cl::desc("Define a threshold to be used"));

// Command line option to specify the function to merge. This is
// mainly used for debugging.
static cl::opt<std::string> ToMergeFile(
    "func-merging-pairs-file", cl::init(""), cl::value_desc("filename"),
    cl::desc("File containing the functions and basic blocks to merge"),
    cl::Hidden);

static std::string GetValueName(const Value *V);

#ifdef __unix__ /* __unix__ is usually defined by compilers targeting Unix     \
                   systems */

unsigned long long getTotalSystemMemory() {
  long pages = sysconf(_SC_PHYS_PAGES);
  long page_size = sysconf(_SC_PAGE_SIZE);
  return pages * page_size;
}

#elif defined(_WIN32) ||                                                       \
    defined(WIN32) /* _Win32 is usually defined by compilers targeting 32 or   \
                      64 bit Windows systems */

unsigned long long getTotalSystemMemory() {
  MEMORYSTATUSEX status;
  status.dwLength = sizeof(status);
  GlobalMemoryStatusEx(&status);
  return status.ullTotalPhys;
}
#endif

class FunctionMerging {
public:
  bool runImpl(Module &M) {
    TargetTransformInfo TTI(M.getDataLayout());
    auto GTTI = [&](Function &F) -> TargetTransformInfo * { return &TTI; };
    return runImpl(M, GTTI);
  }
  bool runImpl(Module &M, function_ref<TargetTransformInfo *(Function &)> GTTI);
};

FunctionMergeResult MergeFunctions(Function *F1, Function *F2) {
  if (F1->getParent() != F2->getParent())
    return FunctionMergeResult(F1, F2, nullptr);
  FunctionMerger Merger(F1->getParent());
  return Merger.merge(F1, F2, "");
}

// Any two pointers in the same address space are equivalent, intptr_t and
// pointers are equivalent. Otherwise, standard type equivalence rules apply.
bool FunctionMerger::areTypesEquivalent(Type *Ty1, Type *Ty2,
                                        const DataLayout *DL) {
  return (Ty1 == Ty2);
}

static bool matchIntrinsicCalls(Intrinsic::ID ID, const CallBase *CI1,
                                const CallBase *CI2) {
  Function *F = CI1->getCalledFunction();
  if (!F)
    return false;
  auto ID1 = (Intrinsic::ID)F->getIntrinsicID();

  F = CI2->getCalledFunction();
  if (!F)
    return false;
  auto ID2 = (Intrinsic::ID)F->getIntrinsicID();

  if (ID1 != ID)
    return false;
  if (ID1 != ID2)
    return false;

  switch (ID) {
  default:
    break;
  case Intrinsic::ctlz: // llvm.ctlz
  case Intrinsic::cttz: // llvm.cttz
    // is_zero_undef argument of bit counting intrinsics must be a constant int
    return CI1->getArgOperand(1) == CI2->getArgOperand(1);
  case Intrinsic::memcpy:
  case Intrinsic::memmove:
  case Intrinsic::memset: {
    // isvolatile argument of memory intrinsics must be a constant int
    return CI1->getArgOperand(3) == CI2->getArgOperand(3);
  }
  case Intrinsic::memcpy_element_unordered_atomic:
  case Intrinsic::memmove_element_unordered_atomic:
  case Intrinsic::memset_element_unordered_atomic: {
    const auto *AMI1 = cast<AtomicMemIntrinsic>(CI1);
    const auto *AMI2 = cast<AtomicMemIntrinsic>(CI2);

    auto *ElementSizeCI1 =
        dyn_cast<ConstantInt>(AMI1->getRawElementSizeInBytes());

    auto *ElementSizeCI2 =
        dyn_cast<ConstantInt>(AMI2->getRawElementSizeInBytes());

    return (ElementSizeCI1 != nullptr && ElementSizeCI1 == ElementSizeCI2);
  }
  case Intrinsic::gcroot:
  case Intrinsic::gcwrite:
  case Intrinsic::gcread:
    // llvm.gcroot parameter #2 must be a constant.
    return CI1->getArgOperand(1) == CI2->getArgOperand(1);
  case Intrinsic::prefetch:
    // arguments #2 and #3 in llvm.prefetch must be constants
    return CI1->getArgOperand(1) == CI2->getArgOperand(1) &&
           CI1->getArgOperand(2) == CI2->getArgOperand(2);
  case Intrinsic::lifetime_start:
  case Intrinsic::lifetime_end:
  case Intrinsic::invariant_start:
    // size argument of memory use markers must be a constant integer
    return CI1->getArgOperand(0) == CI2->getArgOperand(0);
  case Intrinsic::invariant_end:
    // llvm.invariant.end parameter #2 must be a constant integer
    return CI1->getArgOperand(1) == CI2->getArgOperand(1);
  };
  return false;
}

// bool FunctionMerger::matchLandingPad(LandingPadInst *LP1, LandingPadInst
// *LP2) {
static bool matchLandingPad(LandingPadInst *LP1, LandingPadInst *LP2) {
  if (LP1->getType() != LP2->getType())
    return false;
  if (LP1->isCleanup() != LP2->isCleanup())
    return false;
  if (LP1->getNumClauses() != LP2->getNumClauses())
    return false;
  for (unsigned i = 0; i < LP1->getNumClauses(); i++) {
    if (LP1->isCatch(i) != LP2->isCatch(i))
      return false;
    if (LP1->isFilter(i) != LP2->isFilter(i))
      return false;
    if (LP1->getClause(i) != LP2->getClause(i))
      return false;
  }
  return true;
}

static bool matchLoadInsts(const LoadInst *LI1, const LoadInst *LI2) {
  return LI1->isVolatile() == LI2->isVolatile() &&
         LI1->getAlign() == LI2->getAlign() &&
         LI1->getOrdering() == LI2->getOrdering();
}

static bool matchStoreInsts(const StoreInst *SI1, const StoreInst *SI2) {
  return SI1->isVolatile() == SI2->isVolatile() &&
         SI1->getAlign() == SI2->getAlign() &&
         SI1->getOrdering() == SI2->getOrdering();
}

static bool matchAllocaInsts(const AllocaInst *AI1, const AllocaInst *AI2) {
  if (AI1->getArraySize() != AI2->getArraySize() ||
      AI1->getAlign() != AI2->getAlign())
    return false;

#ifdef F3M_FIXES
  return AI1->getAllocatedType() == AI2->getAllocatedType();
#else
  return true;
#endif
}

static bool matchGetElementPtrInsts(const GetElementPtrInst *GEP1,
                                    const GetElementPtrInst *GEP2) {
  Type *Ty1 = GEP1->getSourceElementType();
  SmallVector<Value *, 16> Idxs1(GEP1->idx_begin(), GEP1->idx_end());

  Type *Ty2 = GEP2->getSourceElementType();
  SmallVector<Value *, 16> Idxs2(GEP2->idx_begin(), GEP2->idx_end());

  if (Ty1 != Ty2)
    return false;
  if (Idxs1.size() != Idxs2.size())
    return false;

  if (Idxs1.empty())
    return true;

  for (unsigned i = 1; i < Idxs1.size(); i++) {
    Value *V1 = Idxs1[i];
    Value *V2 = Idxs2[i];

    // structs must have constant indices, therefore they must be constants and
    // must be identical when merging
    if (isa<StructType>(Ty1)) {
      if (V1 != V2)
        return false;
    }
    Ty1 = GetElementPtrInst::getTypeAtIndex(Ty1, V1);
    Ty2 = GetElementPtrInst::getTypeAtIndex(Ty2, V2);
    if (Ty1 != Ty2)
      return false;
  }
  return true;
}

static bool matchSwitchInsts(const SwitchInst *SI1, const SwitchInst *SI2) {
  if (SI1->getNumCases() == SI2->getNumCases()) {
    auto CaseIt1 = SI1->case_begin(), CaseEnd1 = SI1->case_end();
    auto CaseIt2 = SI2->case_begin(), CaseEnd2 = SI2->case_end();
    do {
      auto *Case1 = &*CaseIt1;
      auto *Case2 = &*CaseIt2;
      if (Case1 != Case2)
        return false; // TODO: could allow permutation!
      ++CaseIt1;
      ++CaseIt2;
    } while (CaseIt1 != CaseEnd1 && CaseIt2 != CaseEnd2);
    return true;
  }
  return false;
}

static bool matchCallInsts(const CallBase *CI1, const CallBase *CI2) {
  if (CI1->isInlineAsm() || CI2->isInlineAsm())
    return false;

  // if (CI1->getCalledFunction()==nullptr) return false;

  if (CI1->getCalledFunction() != CI2->getCalledFunction())
    return false;

  if (Function *F = CI1->getCalledFunction()) {
    if (auto ID = (Intrinsic::ID)F->getIntrinsicID()) {
      if (!matchIntrinsicCalls(ID, CI1, CI2))
        return false;
    }
  }

  return CI1->arg_size() == CI2->arg_size() &&
         CI1->getCallingConv() == CI2->getCallingConv() &&
         CI1->getAttributes() == CI2->getAttributes();
}

static bool matchInvokeInsts(const InvokeInst *II1, const InvokeInst *II2) {
  return matchCallInsts(II1, II2) &&
         II1->getCallingConv() == II2->getCallingConv() &&
         II1->getAttributes() == II2->getAttributes() &&
         matchLandingPad(II1->getLandingPadInst(), II2->getLandingPadInst());
}

static bool matchInsertValueInsts(const InsertValueInst *IV1,
                                  const InsertValueInst *IV2) {
  return IV1->getIndices() == IV2->getIndices();
}

static bool matchExtractValueInsts(const ExtractValueInst *EV1,
                                   const ExtractValueInst *EV2) {
  return EV1->getIndices() == EV2->getIndices();
}

static bool matchFenceInsts(const FenceInst *FI1, const FenceInst *FI2) {
  return FI1->getOrdering() == FI2->getOrdering() &&
         FI1->getSyncScopeID() == FI2->getSyncScopeID();
}

bool FunctionMerger::matchInstructions(Instruction *I1, Instruction *I2) {

  if (I1->getOpcode() != I2->getOpcode())
    return false;

  if (I1->getOpcode() == Instruction::CallBr)
    return false;

  // Returns are special cases that can differ in the number of operands
  if (I1->getOpcode() == Instruction::Ret)
    return true;

  // Result type should be the same
  if (I1->getType() != I2->getType())
    return false;

  // Operand number and types should be the same
  if (I1->getNumOperands() != I2->getNumOperands())
    return false;

  for (unsigned i = 0; i < I1->getNumOperands(); i++)
    if (I1->getOperand(i)->getType() != I2->getOperand(i)->getType())
      return false;

  switch (I1->getOpcode()) {
    // case Instruction::Br: return false; //{ return (I1->getNumOperands()==1);
    // }

    // #define MatchCaseInst(Kind, I1, I2) case Instruction::#Kind

  case Instruction::Load:
    return matchLoadInsts(dyn_cast<LoadInst>(I1), dyn_cast<LoadInst>(I2));
  case Instruction::Store:
    return matchStoreInsts(dyn_cast<StoreInst>(I1), dyn_cast<StoreInst>(I2));
  case Instruction::Alloca:
    return matchAllocaInsts(dyn_cast<AllocaInst>(I1), dyn_cast<AllocaInst>(I2));
  case Instruction::GetElementPtr:
    return matchGetElementPtrInsts(dyn_cast<GetElementPtrInst>(I1),
                                   dyn_cast<GetElementPtrInst>(I2));
  case Instruction::Switch:
    return matchSwitchInsts(dyn_cast<SwitchInst>(I1), dyn_cast<SwitchInst>(I2));
  case Instruction::Call:
    return matchCallInsts(dyn_cast<CallInst>(I1), dyn_cast<CallInst>(I2));
  case Instruction::Invoke:
    return matchInvokeInsts(dyn_cast<InvokeInst>(I1), dyn_cast<InvokeInst>(I2));
  case Instruction::InsertValue:
    return matchInsertValueInsts(dyn_cast<InsertValueInst>(I1),
                                 dyn_cast<InsertValueInst>(I2));
  case Instruction::ExtractValue:
    return matchExtractValueInsts(dyn_cast<ExtractValueInst>(I1),
                                  dyn_cast<ExtractValueInst>(I2));
  case Instruction::Fence:
    return matchFenceInsts(dyn_cast<FenceInst>(I1), dyn_cast<FenceInst>(I2));
  case Instruction::AtomicCmpXchg: {
    const AtomicCmpXchgInst *CXI = dyn_cast<AtomicCmpXchgInst>(I1);
    const AtomicCmpXchgInst *CXI2 = cast<AtomicCmpXchgInst>(I2);
    return CXI->isVolatile() == CXI2->isVolatile() &&
           CXI->isWeak() == CXI2->isWeak() &&
           CXI->getSuccessOrdering() == CXI2->getSuccessOrdering() &&
           CXI->getFailureOrdering() == CXI2->getFailureOrdering() &&
           CXI->getSyncScopeID() == CXI2->getSyncScopeID();
  }
  case Instruction::AtomicRMW: {
    const AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I1);
    return RMWI->getOperation() == cast<AtomicRMWInst>(I2)->getOperation() &&
           RMWI->isVolatile() == cast<AtomicRMWInst>(I2)->isVolatile() &&
           RMWI->getOrdering() == cast<AtomicRMWInst>(I2)->getOrdering() &&
           RMWI->getSyncScopeID() == cast<AtomicRMWInst>(I2)->getSyncScopeID();
  }
  default:
    if (auto *CI = dyn_cast<CmpInst>(I1))
      return CI->getPredicate() == cast<CmpInst>(I2)->getPredicate();
    if (isa<OverflowingBinaryOperator>(I1)) {
      if (!isa<OverflowingBinaryOperator>(I2))
        return false;
      if (I1->hasNoUnsignedWrap() != I2->hasNoUnsignedWrap())
        return false;
      if (I1->hasNoSignedWrap() != I2->hasNoSignedWrap())
        return false;
    }
    if (isa<PossiblyExactOperator>(I1)) {
      if (!isa<PossiblyExactOperator>(I2))
        return false;
      if (I1->isExact() != I2->isExact())
        return false;
    }
    if (isa<FPMathOperator>(I1)) {
      if (!isa<FPMathOperator>(I2))
        return false;
      if (I1->isFast() != I2->isFast())
        return false;
      if (I1->hasAllowReassoc() != I2->hasAllowReassoc())
        return false;
      if (I1->hasNoNaNs() != I2->hasNoNaNs())
        return false;
      if (I1->hasNoInfs() != I2->hasNoInfs())
        return false;
      if (I1->hasNoSignedZeros() != I2->hasNoSignedZeros())
        return false;
      if (I1->hasAllowReciprocal() != I2->hasAllowReciprocal())
        return false;
      if (I1->hasAllowContract() != I2->hasAllowContract())
        return false;
      if (I1->hasApproxFunc() != I2->hasApproxFunc())
        return false;
    }
  }

  return true;
}

bool FunctionMerger::match(Value *V1, Value *V2) {
  if (auto *I1 = dyn_cast<Instruction>(V1))
    if (auto *I2 = dyn_cast<Instruction>(V2))
      return matchInstructions(I1, I2);

  if (auto *BB1 = dyn_cast<BasicBlock>(V1))
    if (auto *BB2 = dyn_cast<BasicBlock>(V2))
      return matchBlocks(BB1, BB2);

  return false;
}

bool FunctionMerger::matchBlocks(BasicBlock *BB1, BasicBlock *BB2) {
  if (BB1 == nullptr || BB2 == nullptr)
    return false;
  if (BB1->isLandingPad() || BB2->isLandingPad()) {
    LandingPadInst *LP1 = BB1->getLandingPadInst();
    LandingPadInst *LP2 = BB2->getLandingPadInst();
    if (LP1 == nullptr || LP2 == nullptr)
      return false;
    return matchLandingPad(LP1, LP2);
  }
  return true;
}

bool FunctionMerger::matchWholeBlocks(Value *V1, Value *V2) {
  auto *BB1 = dyn_cast<BasicBlock>(V1);
  auto *BB2 = dyn_cast<BasicBlock>(V2);
  if (BB1 == nullptr || BB2 == nullptr)
    return false;

  if (!matchBlocks(BB1, BB2))
    return false;

  auto It1 = BB1->begin();
  auto It2 = BB2->begin();

  while (isa<PHINode>(*It1) || isa<LandingPadInst>(*It1))
    It1++;
  while (isa<PHINode>(*It2) || isa<LandingPadInst>(*It2))
    It2++;

  while (It1 != BB1->end() && It2 != BB2->end()) {
    if (!matchInstructions(&*It1, &*It2))
      return false;

    It1++;
    It2++;
  }

  if (It1 != BB1->end() || It2 != BB2->end())
    return false;

  return true;
}

static void vectorizeBB(SmallVectorImpl<Value *> &Vec, BasicBlock *BB) {
  Vec.push_back(BB);
  for (Instruction &I : *BB)
    if (!isa<LandingPadInst>(&I) && !isa<PHINode>(&I))
      Vec.push_back(&I);
}

bool FunctionMerger::validMergeTypes(Function *F1, Function *F2) {
  Type *F1Ty = F1->getReturnType();
  Type *F2Ty = F2->getReturnType();
  if (areTypesEquivalent(F1Ty, F2Ty, DL))
    return true;

  return (F1Ty->isVoidTy() || F2Ty->isVoidTy());
}

class Timers {
public:
  enum Name : size_t {
    codegen_linear = 0,
    codegen_align,
    codegen_rank,
    codegen_param,
    codegen_gen,
    codegen_fix,
    codegen_postopt,
    codegen_total,
    preprocess,
    rank,
    verify,
    update,
    total,
    SIZE,
  };

  Timers() = default;

  void start(Name Timer) {
    if (!TimingDebug)
      return;
    IterTimers.at(Timer).startTimer();
    TotalTimers.at(Timer).startTimer();
  }

  void stop(Name Timer) {
    if (!TimingDebug)
      return;
    IterTimers.at(Timer).stopTimer();
    TotalTimers.at(Timer).stopTimer();
  }

  void force_stop(Name Timer) {
    if (!TimingDebug)
      return;

    if (IterTimers.at(Timer).isRunning()) {
      IterTimers.at(Timer).stopTimer();
      TotalTimers.at(Timer).stopTimer();
    }
  }

  void attemptStart() {
    if (!TimingDebug)
      return;
    IterTimers.at(Name::total).startTimer();
  }

  void attemptEnd(bool printStats) {
    if (!TimingDebug)
      return;

    if (IterTimers.at(Name::total).isRunning())
      IterTimers.at(Name::total).stopTimer();

    if (printStats)
      errs() << " TotalTime: "
             << IterTimers[Name::total].getTotalTime().getWallTime() * 1000000
             << " RankingTime: "
             << IterTimers[Name::rank].getTotalTime().getWallTime() * 1000000
             << " AlignTime: "
             << IterTimers[Name::codegen_align].getTotalTime().getWallTime() *
                    1000000
             << " CodegenTime: "
             << (IterTimers[Name::codegen_total].getTotalTime().getWallTime() -
                 IterTimers[Name::codegen_align].getTotalTime().getWallTime()) *
                    1000000
             << " VerifyTime: "
             << IterTimers[Name::verify].getTotalTime().getWallTime() * 1000000
             << " UpdateTime: "
             << IterTimers[Name::update].getTotalTime().getWallTime() * 1000000
             << "\n";

    for (auto &timer : IterTimers) {
      assert(!timer.isRunning());
      timer.clear();
    }
  }

  void mergeStart() {
    if (!TimingDebug)
      return;

    IterTimers.clear();
    TotalTimers.clear();
    for (size_t i = 0; i < Name::SIZE; ++i) {
      IterTimers.emplace_back(Descr[i], Descr[i]);
      TotalTimers.emplace_back(Descr[i], Descr[i]);
    }

    TotalTimers.at(Name::total).startTimer();
  }

  void mergeEnd() {
    if (!TimingDebug)
      return;

    if (TotalTimers.at(Name::total).isRunning())
      TotalTimers.at(Name::total).stopTimer();

    errs() << "Timer:Rank: "
           << TotalTimers[Name::rank].getTotalTime().getWallTime() << "\n";
    errs() << "Timer:CodeGen:Total: "
           << TotalTimers[Name::codegen_total].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:Align: "
           << TotalTimers[Name::codegen_align].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:Align:Rank: "
           << TotalTimers[Name::codegen_rank].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:Param: "
           << TotalTimers[Name::codegen_param].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:Gen: "
           << TotalTimers[Name::codegen_gen].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:Fix: "
           << TotalTimers[Name::codegen_fix].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:CodeGen:PostOpt: "
           << TotalTimers[Name::codegen_postopt].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:Verify: "
           << TotalTimers[Name::verify].getTotalTime().getWallTime() << "\n";
    errs() << "Timer:PreProcess: "
           << TotalTimers[Name::preprocess].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:Lin: "
           << TotalTimers[Name::codegen_linear].getTotalTime().getWallTime()
           << "\n";
    errs() << "Timer:Update: "
           << TotalTimers[Name::update].getTotalTime().getWallTime() << "\n";
    errs() << "Timer:Total: "
           << TotalTimers[Name::total].getTotalTime().getWallTime() << "\n";

    for (auto &timer : TotalTimers) {
      assert(!timer.isRunning());
      timer.clear();
    }

    IterTimers.clear();
    TotalTimers.clear();
  }

private:
  std::vector<Timer> IterTimers;
  std::vector<Timer> TotalTimers;
  std::array<std::string, Name::SIZE> Descr = {"Merge::CodeGen::Lin",
                                               "Merge::CodeGen::Align",
                                               "Merge::CodeGen::Align::Rank",
                                               "Merge::CodeGen::Param",
                                               "Merge::CodeGen::Gen",
                                               "Merge::CodeGen::Fix",
                                               "Merge::CodeGen::PostOpt",
                                               "Merge::CodeGen::Total",
                                               "Merge::Preprocess",
                                               "Merge::Rank",
                                               "Merge::Verify",
                                               "Merge::Update",
                                               "Merge::Total"};
};

Timers MergeTimers{};

static bool validMergePair(Function *F1, Function *F2) {
  if (!HasWholeProgram && (F1->hasAvailableExternallyLinkage() ||
                           F2->hasAvailableExternallyLinkage()))
    return false;

  if (!HasWholeProgram &&
      (F1->hasLinkOnceLinkage() || F2->hasLinkOnceLinkage()))
    return false;

  if (F1->hasComdat() != F2->hasComdat())
    return false;
  if (F1->hasComdat() && F1->getComdat() != F2->getComdat())
    return false;

  if (F1->hasPersonalityFn() != F2->hasPersonalityFn())
    return false;
  if (F1->hasPersonalityFn()) {
    Constant *PersonalityFn1 = F1->getPersonalityFn();
    Constant *PersonalityFn2 = F2->getPersonalityFn();
    if (PersonalityFn1 != PersonalityFn2)
      return false;
  }

  return true;
}

static void MergeArguments(LLVMContext &Context, Function *F1, Function *F2,
                           AlignedCode &AlignedSeq,
                           std::map<unsigned, unsigned> &ParamMap1,
                           std::map<unsigned, unsigned> &ParamMap2,
                           std::vector<Type *> &Args) {

  std::vector<Argument *> ArgsList1;
  for (Argument &arg : F1->args()) {
    ArgsList1.push_back(&arg);
  }

  Args.push_back(IntegerType::get(Context, 1)); // push the function Id argument
  unsigned ArgId = 0;
  for (auto I = F1->arg_begin(), E = F1->arg_end(); I != E; I++) {
    ParamMap1[ArgId] = Args.size();
    Args.push_back((*I).getType());
    ArgId++;
  }

  auto AttrList1 = F1->getAttributes();
  auto AttrList2 = F2->getAttributes();

  // merge arguments from Function2 with Function1
  ArgId = 0;
  for (auto I = F2->arg_begin(), E = F2->arg_end(); I != E; I++) {

    std::map<unsigned, int> MatchingScore;
    // first try to find an argument with the same name/type
    // otherwise try to match by type only
    for (unsigned i = 0; i < ArgsList1.size(); i++) {
      if (ArgsList1[i]->getType() == (*I).getType()) {

        auto AttrSet1 = AttrList1.getParamAttrs(ArgsList1[i]->getArgNo());
        auto AttrSet2 = AttrList2.getParamAttrs((*I).getArgNo());
        if (AttrSet1 != AttrSet2)
          continue;

        bool hasConflict = false; // check for conflict from a previous matching
        for (auto ParamPair : ParamMap2) {
          if (ParamPair.second == ParamMap1[i]) {
            hasConflict = true;
            break;
          }
        }
        if (hasConflict)
          continue;
        MatchingScore[i] = 0;
      }
    }

    if (MatchingScore.size() > 0) { // maximize scores
      for (auto &Entry : AlignedSeq) {
        if (Entry.match()) {
          auto *I1 = dyn_cast<Instruction>(Entry.get(0));
          auto *I2 = dyn_cast<Instruction>(Entry.get(1));
          if (I1 != nullptr && I2 != nullptr) { // test both for sanity
            for (unsigned i = 0; i < I1->getNumOperands(); i++) {
              for (auto KV : MatchingScore) {
                if (I1->getOperand(i) == ArgsList1[KV.first]) {
                  if (i < I2->getNumOperands() && I2->getOperand(i) == &(*I)) {
                    MatchingScore[KV.first]++;
                  }
                }
              }
            }
          }
        }
      }

      int MaxScore = -1;
      unsigned MaxId = 0;

      for (auto KV : MatchingScore) {
        if (KV.second > MaxScore) {
          MaxScore = KV.second;
          MaxId = KV.first;
        }
      }

      ParamMap2[ArgId] = ParamMap1[MaxId];
    } else {
      ParamMap2[ArgId] = Args.size();
      Args.push_back((*I).getType());
    }

    ArgId++;
  }
}

static void SetFunctionAttributes(Function *F1, Function *F2,
                                  Function *MergedFunc) {
  unsigned MaxAlignment = std::max(F1->getAlignment(), F2->getAlignment());
  if (F1->getAlignment() != F2->getAlignment()) {
    if (Verbose)
      errs() << "WARNING: different function alignment!\n";
  }
  if (MaxAlignment)
    MergedFunc->setAlignment(Align(MaxAlignment));

  if (F1->getCallingConv() == F2->getCallingConv()) {
    MergedFunc->setCallingConv(F1->getCallingConv());
  } else {
    if (Verbose)
      errs() << "WARNING: different calling convention!\n";
  }

  if (F1->getLinkage() == F2->getLinkage()) {
    MergedFunc->setLinkage(F1->getLinkage());
  } else {
    if (Verbose)
      errs() << "WARNING: different linkage type!\n";
    MergedFunc->setLinkage(GlobalValue::LinkageTypes::InternalLinkage);
  }

  /*
  if (F1->isDSOLocal() == F2->isDSOLocal()) {
    MergedFunc->setDSOLocal(F1->isDSOLocal());
  } else {
    if (Verbose)
      errs() << "WARNING: different DSO local!\n";
  }
  */
  MergedFunc->setDSOLocal(true);

  if (F1->getSubprogram() == F2->getSubprogram()) {
    MergedFunc->setSubprogram(F1->getSubprogram());
  } else {
    if (Verbose)
      errs() << "WARNING: different subprograms!\n";
  }

  /*
    if (F1->getUnnamedAddr() == F2->getUnnamedAddr()) {
      MergedFunc->setUnnamedAddr(F1->getUnnamedAddr());
    } else {
      if (Verbose)
        errs() << "WARNING: different unnamed addr!\n";
      MergedFunc->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);
    }
  */
  // MergedFunc->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);

  /*
  if (F1->getVisibility() == F2->getVisibility()) {
    //MergedFunc->setVisibility(F1->getVisibility());
  } else {
    if (Verbose)
      errs() << "WARNING: different visibility!\n";
  }
  */
  MergedFunc->setVisibility(GlobalValue::VisibilityTypes::DefaultVisibility);

  // Exception Handling requires landing pads to have the same personality
  // function
  if (F1->hasPersonalityFn() && F2->hasPersonalityFn()) {
    Constant *PersonalityFn1 = F1->getPersonalityFn();
    Constant *PersonalityFn2 = F2->getPersonalityFn();
    if (PersonalityFn1 == PersonalityFn2) {
      MergedFunc->setPersonalityFn(PersonalityFn1);
    } else {
      if (Verbose)
        errs() << "WARNING: different personality function!\n";
      if (Debug) {
        PersonalityFn1->dump();
        PersonalityFn2->dump();
      }
    }
  } else if (F1->hasPersonalityFn()) {
    if (Verbose)
      // TODO: check if this is valid: merge function with personality with
      // function without it
      MergedFunc->setPersonalityFn(F1->getPersonalityFn());
    if (Verbose)
      errs() << "WARNING: only one personality function!\n";
  } else if (F2->hasPersonalityFn()) {
    // TODO: check if this is valid: merge function with personality with
    // function without it
    MergedFunc->setPersonalityFn(F2->getPersonalityFn());
    if (Verbose)
      errs() << "WARNING: only one personality function!\n";
  }

  if (F1->hasComdat() && F2->hasComdat()) {
    auto *Comdat1 = F1->getComdat();
    auto *Comdat2 = F2->getComdat();
    if (Comdat1 == Comdat2) {
      MergedFunc->setComdat(Comdat1);
    } else if (Verbose) {
      errs() << "WARNING: different comdats!\n";
    }
  } else if (F1->hasComdat()) {
    MergedFunc->setComdat(F1->getComdat()); // TODO: check if this is valid:
                                            // merge function with comdat with
                                            // function without it
    if (Verbose)
      errs() << "WARNING: only one comdat!\n";
  } else if (F2->hasComdat()) {
    MergedFunc->setComdat(F2->getComdat()); // TODO: check if this is valid:
                                            // merge function with comdat with
                                            // function without it
    if (Verbose)
      errs() << "WARNING: only one comdat!\n";
  }

  if (F1->hasSection()) {
    MergedFunc->setSection(F1->getSection());
  }
}

unsigned instToInt(Instruction *I);

inst_range getInstructions(Function *F) { return instructions(F); }

iterator_range<BasicBlock::iterator> getInstructions(BasicBlock *BB) {
  return make_range(BB->begin(), BB->end());
}

template <class T> class FingerprintMH {
private:
  // The number of instructions defining a shingle. 2 or 3 is best.
  static constexpr size_t K = 2;
  static constexpr double threshold = 0.3;
  static constexpr size_t MaxOpcode = 68;
  const uint32_t _footprint;

public:
  uint64_t magnitude{0};
  std::vector<uint32_t> hash;
  std::vector<uint32_t> bandHash;

public:
  FingerprintMH() = default;

  FingerprintMH(T owner, SearchStrategy &searchStrategy)
      : _footprint(searchStrategy.item_footprint()) {
    std::vector<uint32_t> integers;
    std::array<uint32_t, MaxOpcode> OpcodeFreq;

    for (size_t i = 0; i < MaxOpcode; i++)
      OpcodeFreq[i] = 0;

    // Shingles crossing basic block boundaries shouldn't work well
    // but it does and it's simpler

    for (Instruction &I : getInstructions(owner)) {
      integers.push_back(instToInt(&I));
      OpcodeFreq[I.getOpcode()]++;
      if (I.isTerminator())
        OpcodeFreq[0] += I.getNumSuccessors();
    }

    for (size_t i = 0; i < MaxOpcode; ++i) {
      uint64_t val = OpcodeFreq[i];
      magnitude += val * val;
    }

    searchStrategy.generateShinglesMultipleHashPipelineTurbo<K>(integers, hash);
    searchStrategy.generateBands(hash, bandHash);
  }

  uint32_t footprint() const { return _footprint; }

  float distance(const FingerprintMH &FP2) const {
    size_t nintersect = 0;
    size_t pos1 = 0;
    size_t pos2 = 0;
    size_t nHashes = hash.size();

    while (pos1 != nHashes && pos2 != nHashes) {
      if (hash[pos1] == FP2.hash[pos2]) {
        nintersect++;
        pos1++;
        pos2++;
      } else if (hash[pos1] < FP2.hash[pos2]) {
        pos1++;
      } else {
        pos2++;
      }
    }

    int nunion = 2 * nHashes - nintersect;
    return 1.f - (nintersect / (float)nunion);
  }

  float distance_under(const FingerprintMH &FP2, float best_distance) const {
    size_t mismatches = 0;
    size_t pos1 = 0;
    size_t pos2 = 0;
    size_t nHashes = hash.size();
    size_t best_nintersect = static_cast<size_t>(
        2.0 * nHashes * (1.f - best_distance) / (2.f - best_distance));
    size_t best_mismatches = 2 * (nHashes - best_nintersect);

    while (pos1 != nHashes && pos2 != nHashes) {
      if (hash[pos1] == FP2.hash[pos2]) {
        pos1++;
        pos2++;
      } else if (hash[pos1] < FP2.hash[pos2]) {
        mismatches++;
        pos1++;
      } else {
        mismatches++;
        pos2++;
      }
      if (mismatches > best_mismatches)
        break;
    }

    size_t nintersect = nHashes - (mismatches / 2);
    int nunion = 2 * nHashes - nintersect;
    return 1.f - (nintersect / (float)nunion);
  }
};

template <class T> class Fingerprint {
public:
  uint64_t magnitude{0};
  static const size_t MaxOpcode = 68;
  std::array<uint32_t, MaxOpcode> OpcodeFreq;

  Fingerprint() = default;

  Fingerprint(T owner) {
    // memset(OpcodeFreq, 0, sizeof(int) * MaxOpcode);
    for (size_t i = 0; i < MaxOpcode; i++)
      OpcodeFreq[i] = 0;

    for (Instruction &I : getInstructions(owner)) {
      OpcodeFreq[I.getOpcode()]++;
      if (I.isTerminator())
        OpcodeFreq[0] += I.getNumSuccessors();
    }
    for (size_t i = 0; i < MaxOpcode; i++) {
      uint64_t val = OpcodeFreq[i];
      magnitude += val * val;
    }
  }

  uint32_t footprint() const { return sizeof(int) * MaxOpcode; }

  float distance(const Fingerprint &FP2) const {
    int Distance = 0;
    for (size_t i = 0; i < MaxOpcode; i++) {
      int Freq1 = OpcodeFreq[i];
      int Freq2 = FP2.OpcodeFreq[i];
      Distance += std::abs(Freq1 - Freq2);
    }
    return static_cast<float>(Distance);
  }
};

class BlockFingerprint : public Fingerprint<BasicBlock *> {
public:
  BasicBlock *BB{nullptr};
  size_t Size{0};

  BlockFingerprint(BasicBlock *BB) : Fingerprint(BB), BB(BB) {
    for (Instruction &I : *BB) {
      if (!isa<LandingPadInst>(&I) && !isa<PHINode>(&I)) {
        Size++;
      }
    }
  }
};

template <class T> class MatchInfo {
public:
  T candidate{nullptr};
  size_t Size{0};
  size_t OtherSize{0};
  size_t MergedSize{0};
  size_t Magnitude{0};
  size_t OtherMagnitude{0};
  float Distance{0};
  bool Valid{false};
  bool Profitable{false};

  MatchInfo() = default;
  MatchInfo(T candidate) : candidate(candidate) {};
  MatchInfo(T candidate, size_t Size) : candidate(candidate), Size(Size) {};
};

template <class T> class Matcher {
public:
  Matcher() = default;
  virtual ~Matcher() = default;

  virtual void add_candidate(T candidate, size_t size) = 0;
  virtual void remove_candidate(T candidate) = 0;
  virtual T next_candidate() = 0;
  virtual MatchInfo<T> get_match(T candidate) = 0;
  virtual size_t size() = 0;
  virtual void print_stats() = 0;
};

template <class T, template <typename> class FPTy = Fingerprint>
class MatcherManual : public Matcher<T> {
private:
  struct MatcherEntry {
    T candidate;
    size_t size;
    FPTy<T> FP;
    MatcherEntry() : MatcherEntry(nullptr, 0) {};

    template <typename T1 = FPTy<T>, typename T2 = Fingerprint<T>>
    MatcherEntry(
        T candidate, size_t size,
        typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr)
        : candidate(candidate), size(size), FP(candidate) {}

    template <typename T1 = FPTy<T>, typename T2 = FingerprintMH<T>>
    MatcherEntry(
        T candidate, size_t size, SearchStrategy &strategy,
        typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr)
        : candidate(candidate), size(size), FP(candidate, strategy) {}
  };
  using MatcherIt = typename std::list<MatcherEntry>::iterator;

  bool initialized{false};
  FunctionMerger &FM;
  std::list<MatcherEntry> candidates;
  MatcherIt match_handle;
  std::unordered_map<std::string, std::string> matchNames;

public:
  MatcherManual() = default;
  MatcherManual(FunctionMerger &FM, std::string Filename)
      : FM(FM), match_handle{candidates.end()} {
    std::ifstream File{Filename};
    std::string FuncName1, FuncName2;
    while (File >> FuncName1 >> FuncName2) {
      matchNames[FuncName1] = FuncName2;
      matchNames[FuncName2] = FuncName1;
    }
  }

  virtual ~MatcherManual() = default;

  void add_candidate(T candidate, size_t size) override {
    if (matchNames.count(GetValueName(candidate)) == 0)
      return;
    add_candidate_helper(candidate, size);
  }

  template <typename T1 = FPTy<T>, typename T2 = Fingerprint<T>>
  void add_candidate_helper(
      T candidate, size_t size,
      typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr) {
    candidates.emplace_front(candidate, size);
  }

  void remove_candidate(T candidate) override {
    // candidate will either be the front candidate or its match

    // Try the front
    MatcherIt it = candidates.begin();
    assert(it != candidates.end());

    if (it->candidate != candidate) {
      // Try the match
      it = match_handle;
      assert(it != candidates.end());
      assert(it->candidate == candidate);
      match_handle = candidates.end();
    }
    candidates.erase(it);
  }

  T next_candidate() override {
    if (!initialized) {
      candidates.sort([&](auto &item1, auto &item2) -> bool {
        return item1.FP.magnitude > item2.FP.magnitude;
      });
      initialized = true;
    }
    return candidates.front().candidate;
  }

  MatchInfo<T> get_match(T candidate) override {
    MatchInfo<T> best_match;
    auto it = candidates.begin();
    best_match.OtherSize = it->size;
    best_match.OtherMagnitude = it->FP.magnitude;
    best_match.Distance = std::numeric_limits<float>::max();

    for (auto entry = std::next(candidates.begin()); entry != candidates.end();
         ++entry) {
      if (!FM.validMergeTypes(it->candidate, entry->candidate) ||
          !validMergePair(it->candidate, entry->candidate))
        continue;
      if (matchNames[GetValueName(it->candidate)] ==
          GetValueName(entry->candidate)) {
        best_match.candidate = entry->candidate;
        best_match.Size = entry->size;
        best_match.Magnitude = entry->FP.magnitude;
        best_match.Distance = 0;
        match_handle = entry;
        break;
      }
    }
    return best_match;
  }

  size_t size() override { return candidates.size(); }

  void print_stats() override {
    int Sum = 0;
    int Count = 0;
    float MinDistance = std::numeric_limits<float>::max();
    float MaxDistance = 0;

    int Index1 = 0;
    for (auto It1 = candidates.begin(), E1 = candidates.end(); It1 != E1;
         It1++) {

      int BestIndex = 0;
      bool FoundCandidate = false;
      float BestDist = std::numeric_limits<float>::max();

      int Index2 = Index1;
      for (auto It2 = It1, E2 = candidates.end(); It2 != E2; It2++) {

        if (It1->candidate == It2->candidate || Index1 == Index2) {
          Index2++;
          continue;
        }

        if (!FM.validMergeTypes(It1->candidate, It2->candidate) ||
            !validMergePair(It1->candidate, It2->candidate))
          continue;

        auto Dist = It1->FP.distance(It2->FP);
        if (Dist < BestDist) {
          BestDist = Dist;
          FoundCandidate = true;
          BestIndex = Index2;
        }
        Index2++;
      }
      if (FoundCandidate) {
        int Distance = std::abs(Index1 - BestIndex);
        Sum += Distance;
        if (Distance > MaxDistance)
          MaxDistance = Distance;
        if (Distance < MinDistance)
          MinDistance = Distance;
        Count++;
      }
      Index1++;
    }
    errs() << "Total: " << Count << "\n";
    errs() << "Min Distance: " << MinDistance << "\n";
    errs() << "Max Distance: " << MaxDistance << "\n";
    errs() << "Average Distance: " << (((double)Sum) / ((double)Count)) << "\n";
  }
};

template <class T, template <typename> class FPTy = Fingerprint>
class MatcherFQ : public Matcher<T> {
private:
  struct MatcherEntry {
    T candidate;
    size_t size;
    FPTy<T> FP;
    MatcherEntry() : MatcherEntry(nullptr, 0) {};

    template <typename T1 = FPTy<T>, typename T2 = Fingerprint<T>>
    MatcherEntry(
        T candidate, size_t size,
        typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr)
        : candidate(candidate), size(size), FP(candidate) {}

    template <typename T1 = FPTy<T>, typename T2 = FingerprintMH<T>>
    MatcherEntry(
        T candidate, size_t size, SearchStrategy &strategy,
        typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr)
        : candidate(candidate), size(size), FP(candidate, strategy) {}
  };
  using MatcherIt = typename std::list<MatcherEntry>::iterator;

  bool initialized{false};
  FunctionMerger &FM;
  std::list<MatcherEntry> candidates;
  MatcherIt match_handle;
  SearchStrategy strategy;

public:
  MatcherFQ() = default;
  MatcherFQ(FunctionMerger &FM, size_t rows = 2, size_t bands = 100)
      : FM(FM), strategy(rows, bands) {};

  virtual ~MatcherFQ() = default;

  void add_candidate(T candidate, size_t size) override {
    add_candidate_helper(candidate, size);
  }

  template <typename T1 = FPTy<T>, typename T2 = Fingerprint<T>>
  void add_candidate_helper(
      T candidate, size_t size,
      typename std::enable_if_t<std::is_same<T1, T2>::value, int> * = nullptr) {
    candidates.emplace_front(candidate, size);
  }

  template <typename T1 = FPTy<T>, typename T2 = Fingerprint<T>>
  void add_candidate_helper(
      T candidate, size_t size,
      typename std::enable_if_t<!std::is_same<T1, T2>::value, int> * =
          nullptr) {
    candidates.emplace_front(candidate, size, strategy);
  }

  void remove_candidate(T candidate) override {
    // candidate will either be the front candidate or its match

    // Try the front
    MatcherIt it = candidates.begin();
    assert(it != candidates.end());

    if (it->candidate != candidate) {
      // Try the match
      it = match_handle;
      assert(it != candidates.end());
      assert(it->candidate == candidate);
      match_handle = candidates.end();
    }
    candidates.erase(it);
  }

  T next_candidate() override {
    if (!initialized) {
      candidates.sort([&](auto &item1, auto &item2) -> bool {
        return item1.FP.magnitude > item2.FP.magnitude;
      });
      initialized = true;
    }
    return candidates.front().candidate;
  }

  MatchInfo<T> get_match(T candidate) override {
    MatchInfo<T> best_match;
    MatcherIt it = candidates.begin();
    best_match.OtherSize = it->size;
    best_match.OtherMagnitude = it->FP.magnitude;
    best_match.Distance = std::numeric_limits<float>::max();

    for (auto entry = std::next(candidates.begin()); entry != candidates.end();
         ++entry) {
      if (!FM.validMergeTypes(it->candidate, entry->candidate) ||
          !validMergePair(it->candidate, entry->candidate))
        continue;
      auto new_distance = it->FP.distance(entry->FP);
      if (new_distance < best_match.Distance) {
        best_match.candidate = entry->candidate;
        best_match.Size = entry->size;
        best_match.Magnitude = entry->FP.magnitude;
        best_match.Distance = new_distance;
        match_handle = entry;
      }
    }

    // Ignore the candidate if using F3M and it's above the distance threshold
    if (EnableF3M && best_match.Distance >= RankingDistance) {
      best_match.candidate = nullptr;
      match_handle = candidates.end();
    }

    return best_match;
  }

  size_t size() override { return candidates.size(); }

  void print_stats() override {
    int Sum = 0;
    int Count = 0;
    float MinDistance = std::numeric_limits<float>::max();
    float MaxDistance = 0;

    int Index1 = 0;
    for (auto It1 = candidates.begin(), E1 = candidates.end(); It1 != E1;
         It1++) {

      int BestIndex = 0;
      bool FoundCandidate = false;
      float BestDist = std::numeric_limits<float>::max();

      int Index2 = Index1;
      for (auto It2 = It1, E2 = candidates.end(); It2 != E2; It2++) {

        if (It1->candidate == It2->candidate || Index1 == Index2) {
          Index2++;
          continue;
        }

        if (!FM.validMergeTypes(It1->candidate, It2->candidate) ||
            !validMergePair(It1->candidate, It2->candidate))
          continue;

        auto Dist = It1->FP.distance(It2->FP);
        if (Dist < BestDist) {
          BestDist = Dist;
          FoundCandidate = true;
          BestIndex = Index2;
        }
        Index2++;
      }
      if (FoundCandidate) {
        int Distance = std::abs(Index1 - BestIndex);
        Sum += Distance;
        if (Distance > MaxDistance)
          MaxDistance = Distance;
        if (Distance < MinDistance)
          MinDistance = Distance;
        Count++;
      }
      Index1++;
    }
    errs() << "Total: " << Count << "\n";
    errs() << "Min Distance: " << MinDistance << "\n";
    errs() << "Max Distance: " << MaxDistance << "\n";
    errs() << "Average Distance: " << (((double)Sum) / ((double)Count)) << "\n";
  }
};

template <class T> class MatcherLSH : public Matcher<T> {
private:
  struct MatcherEntry {
    T candidate;
    size_t size;
    FingerprintMH<T> FP;
    MatcherEntry() : MatcherEntry(nullptr, 0) {};
    MatcherEntry(T candidate, size_t size, SearchStrategy &strategy)
        : candidate(candidate), size(size), FP(candidate, strategy) {};
  };
  using MatcherIt = typename std::list<MatcherEntry>::iterator;

  bool initialized{false};
  const size_t rows{2};
  const size_t bands{100};
  FunctionMerger &FM;
  SearchStrategy strategy;

  std::list<MatcherEntry> candidates;
  std::unordered_map<uint32_t, std::vector<MatcherIt>> lsh;
  MatcherIt match_handle;

public:
  MatcherLSH() = default;
  MatcherLSH(FunctionMerger &FM, size_t rows, size_t bands)
      : rows(rows), bands(bands), FM(FM), strategy(rows, bands),
        match_handle(candidates.end()) {};

  virtual ~MatcherLSH() = default;

  void add_candidate(T candidate, size_t size) override {
    candidates.emplace_front(candidate, size, strategy);

    auto it = candidates.begin();
    auto &bandHash = it->FP.bandHash;
    for (size_t i = 0; i < bands; ++i) {
      if (lsh.count(bandHash[i]) > 0)
        lsh.at(bandHash[i]).push_back(it);
      else
        lsh.insert(std::make_pair(bandHash[i], std::vector<MatcherIt>(1, it)));
    }
  }

  void remove_candidate(T candidate) override {
    // candidate will either be the front candidate or its match

    // Try the front
    MatcherIt it = candidates.begin();
    assert(it != candidates.end());

    if (it->candidate != candidate) {
      // Try the match
      it = match_handle;
      assert(it != candidates.end());
      assert(it->candidate == candidate);
      match_handle = candidates.end();
    }

    auto &FP = it->FP;
    for (size_t i = 0; i < bands; ++i) {
      if (lsh.count(FP.bandHash[i]) == 0)
        continue;

      auto &foundFs = lsh.at(FP.bandHash[i]);
      for (size_t j = 0; j < foundFs.size(); ++j)
        if (foundFs[j]->candidate == candidate)
          lsh.at(FP.bandHash[i]).erase(lsh.at(FP.bandHash[i]).begin() + j);
    }
    candidates.erase(it);
  }

  T next_candidate() override {
    if (!initialized) {
      candidates.sort([&](auto &item1, auto &item2) -> bool {
        return item1.FP.magnitude > item2.FP.magnitude;
      });
      initialized = true;
    }
    return candidates.front().candidate;
  }

  MatchInfo<T> get_match(T candidate) override {
    std::unordered_set<T> seen;
    seen.reserve(candidates.size() / 10);

    MatcherIt it = candidates.begin();
    auto &FP = it->FP;
    MatchInfo<T> best_match;
    best_match.Distance = std::numeric_limits<float>::max();
    for (size_t i = 0; i < bands; ++i) {
      assert(lsh.count(FP.bandHash[i]) > 0);

      auto &foundFs = lsh.at(FP.bandHash[i]);
      for (size_t j = 0; j < foundFs.size() && j < BucketSizeCap; ++j) {
        auto match_it = foundFs[j];
        if ((match_it->candidate == NULL) ||
            (match_it->candidate == it->candidate))
          continue;
        if (!FM.validMergeTypes(it->candidate, match_it->candidate) ||
            !validMergePair(it->candidate, match_it->candidate))
          continue;

        if (seen.count(match_it->candidate) == 1)
          continue;
        seen.insert(match_it->candidate);

        MatchInfo<T> new_match(match_it->candidate, match_it->size);
        if (best_match.Distance < 0.1)
          new_match.Distance =
              FP.distance_under(match_it->FP, best_match.Distance);
        else
          new_match.Distance = FP.distance(match_it->FP);
        new_match.OtherSize = it->size;
        new_match.OtherMagnitude = FP.magnitude;
        new_match.Magnitude = match_it->FP.magnitude;
        if (new_match.Distance < best_match.Distance &&
            new_match.Distance < RankingDistance) {
          best_match = new_match;
          match_handle = match_it;
        }
      }
      // If we've gone through i = 0 without finding a distance of 0.0
      // the minimum distance we might ever find is 2.0 / (nHashes + 1)
      if (best_match.Distance < (2.0 / (rows * bands)))
        break;
    }
    return best_match;
  }

  size_t size() override { return candidates.size(); }

  void print_stats() override {
    std::vector<uint32_t> hist_bucket_size(20);

    for (auto it = lsh.cbegin(); it != lsh.cend(); ++it) {
      size_t idx = 31 - __builtin_clz(it->second.size());
      idx = idx < 20 ? idx : 19;
      hist_bucket_size[idx]++;
    }

    for (size_t i = 0; i < 20; i++)
      errs() << "STATS: Histogram Bucket Size " << (1 << i) << " : "
             << hist_bucket_size[i] << "\n";
  }
};

template <class T> class MatcherReport {
private:
  struct MatcherEntry {
    T candidate;
    Fingerprint<T> FPF;
    FingerprintMH<T> FPMH;
    MatcherEntry(T candidate, SearchStrategy &strategy)
        : candidate(candidate), FPF(candidate), FPMH(candidate, strategy) {};
  };
  using MatcherIt = typename std::list<MatcherEntry>::iterator;

  FunctionMerger &FM;
  SearchStrategy strategy;
  std::vector<MatcherEntry> candidates;

public:
  MatcherReport() = default;
  MatcherReport(size_t rows, size_t bands, FunctionMerger &FM)
      : FM(FM), strategy(rows, bands) {};

  ~MatcherReport() = default;

  void add_candidate(T candidate) {
    candidates.emplace_back(candidate, strategy);
  }

  void report() const {
    char distance_mh_str[20];

    for (auto &entry : candidates) {
      uint64_t val = 0;
      for (auto &num : entry.FPF.OpcodeFreq)
        val += num;
      errs() << "Function Name: " << GetValueName(entry.candidate)
             << " Fingerprint Size: " << val << "\n";
    }

    std::string Name("_m_f_");
    for (auto it1 = candidates.cbegin(); it1 != candidates.cend(); ++it1) {
      for (auto it2 = std::next(it1); it2 != candidates.cend(); ++it2) {
        if (!FM.validMergeTypes(it1->candidate, it2->candidate) ||
            !validMergePair(it1->candidate, it2->candidate))
          continue;

        auto distance_fq = it1->FPF.distance(it2->FPF);
        auto distance_mh = it1->FPMH.distance(it2->FPMH);
        std::snprintf(distance_mh_str, 20, "%.5f", distance_mh);
        errs() << "F1: " << it1 - candidates.cbegin() << " + "
               << "F2: " << it2 - candidates.cbegin() << " "
               << "FQ: " << static_cast<int>(distance_fq) << " "
               << "MH: " << distance_mh_str << "\n";
        FunctionMergeResult Result =
            FM.merge(it1->candidate, it2->candidate, Name);
      }
    }
  }
};

AlignedCode::AlignedCode(BasicBlock *BB1, BasicBlock *BB2) {
  // this should never happen
  assert(BB1 != nullptr || BB2 != nullptr);

  // Add only BB1, skipping Phi nodes and Landing Pads
  if (BB1 != nullptr && BB2 == nullptr) {
    Data.emplace_back(BB1, nullptr, false);
    for (Instruction &I : *BB1) {
      if (isa<PHINode>(&I) || isa<LandingPadInst>(&I))
        continue;
      Data.emplace_back(&I, nullptr, false);
    }
    return;
  }

  // Add only BB2, skipping Phi nodes and Landing Pads
  if (BB1 == nullptr && BB2 != nullptr) {
    Data.emplace_back(nullptr, BB2, false);
    for (Instruction &I : *BB2) {
      if (isa<PHINode>(&I) || isa<LandingPadInst>(&I))
        continue;
      Data.emplace_back(nullptr, &I, false);
    }
    return;
  }

  // Add both, skipping Phi nodes and Landing Pads
  Data.emplace_back(BB1, BB2, FunctionMerger::matchBlocks(BB1, BB2));

  auto It1 = BB1->begin();
  while (isa<PHINode>(*It1) || isa<LandingPadInst>(*It1))
    It1++;

  auto It2 = BB2->begin();
  while (isa<PHINode>(*It2) || isa<LandingPadInst>(*It2))
    It2++;

  while (It1 != BB1->end() && It2 != BB2->end()) {
    Instruction *I1 = &*It1;
    Instruction *I2 = &*It2;

    if (FunctionMerger::matchInstructions(I1, I2)) {
      Data.emplace_back(I1, I2, true);
    } else {
      Data.emplace_back(I1, nullptr, false);
      Data.emplace_back(nullptr, I2, false);
    }

    It1++;
    It2++;
  }
  assert((It1 == BB1->end()) && (It2 == BB2->end()));
}

bool AlignedCode::isProfitable() const {
  int OriginalCost = 0;
  int MergedCost = 0;

  bool InsideSplit = false;

  for (auto &Entry : Data) {
    Instruction *I1 = nullptr;
    if (Entry.get(0))
      I1 = dyn_cast<Instruction>(Entry.get(0));

    Instruction *I2 = nullptr;
    if (Entry.get(1))
      I2 = dyn_cast<Instruction>(Entry.get(1));

    bool IsInstruction = I1 != nullptr || I2 != nullptr;
    if (Entry.match()) {
      if (IsInstruction) {
        OriginalCost += 2;
        MergedCost += 1;
      }
      if (InsideSplit) {
        InsideSplit = false;
        MergedCost += 2;
      }
    } else {
      if (IsInstruction) {
        OriginalCost += 1;
        MergedCost += 1;
      }
      if (!InsideSplit) {
        InsideSplit = true;
        MergedCost += 1;
      }
    }
  }

  bool Profitable = (MergedCost <= OriginalCost);
  if (Verbose)
    errs() << ((Profitable) ? "Profitable" : "Unprofitable") << "\n";
  return Profitable;
}

void AlignedCode::extend(const AlignedCode &Other) {
  for (auto &Entry : Other) {
    Instruction *I1 = nullptr;
    if (Entry.get(0))
      I1 = dyn_cast<Instruction>(Entry.get(0));

    Instruction *I2 = nullptr;
    if (Entry.get(1))
      I2 = dyn_cast<Instruction>(Entry.get(1));

    bool IsInstruction = I1 != nullptr || I2 != nullptr;

    Data.emplace_back(Entry.get(0), Entry.get(1), Entry.match());

    if (IsInstruction) {
      Insts++;
      if (Entry.match()) {
        Matches++;
        Instruction *I = I1 ? I1 : I2;
        if (!I->isTerminator())
          CoreMatches++;
      }
    }
  }
}

void AlignedCode::dump() const {
  for (auto &Entry : Data) {
    if (Entry.match()) {
      errs() << "1: ";
      if (isa<BasicBlock>(Entry.get(0)))
        errs() << "BB " << GetValueName(Entry.get(0)) << "\n";
      else
        Entry.get(0)->dump();
      errs() << "2: ";
      if (isa<BasicBlock>(Entry.get(1)))
        errs() << "BB " << GetValueName(Entry.get(1)) << "\n";
      else
        Entry.get(1)->dump();
      errs() << "----\n";
    } else {
      if (Entry.get(0)) {
        errs() << "1: ";
        if (isa<BasicBlock>(Entry.get(0)))
          errs() << "BB " << GetValueName(Entry.get(0)) << "\n";
        else
          Entry.get(0)->dump();
        errs() << "2: -\n";
      } else if (Entry.get(1)) {
        errs() << "1: -\n";
        errs() << "2: ";
        if (isa<BasicBlock>(Entry.get(1)))
          errs() << "BB " << GetValueName(Entry.get(1)) << "\n";
        else
          Entry.get(1)->dump();
      }
      errs() << "----\n";
    }
  }
}

std::optional<AlignedCode> FunctionMerger::align(Function *F1, Function *F2) {

  AlignedCode AlignedSeq;
  NeedlemanWunschSA<SmallVectorImpl<Value *>> SA(ScoringSystem(-1, 2),
                                                 FunctionMerger::match);

  // Old alignment options are removed
  // Can now be only NW or PA
  assert(EnableNW || EnablePA);

  int NumBB1{0}, NumBB2{0};

  MergeTimers.start(Timers::Name::codegen_rank);

  // Fingerprints for all Blocks in F1 organized by size
  std::map<size_t, std::vector<BlockFingerprint>> Blocks;
  for (BasicBlock &BB1 : *F1) {
    BlockFingerprint BD1(&BB1);
    NumBB1++;
    Blocks[BD1.Size].push_back(std::move(BD1));
  }

  MergeTimers.stop(Timers::Name::codegen_rank);

  for (BasicBlock &BIt : *F2) {
    MergeTimers.start(Timers::Name::codegen_rank);

    BasicBlock *BB2 = &BIt;
    BlockFingerprint BD2(BB2);
    NumBB2++;

    // list all the map entries in Blocks in order of distance from BD2.Size
    auto ItSetIncr = Blocks.lower_bound(BD2.Size);
    auto ItSetDecr = std::reverse_iterator(ItSetIncr);
    std::vector<decltype(ItSetIncr)> ItSets;

    if (EnableNW) {
      while (ItSetDecr != Blocks.rend() && ItSetIncr != Blocks.end()) {
        if (BD2.Size - ItSetDecr->first < ItSetIncr->first - BD2.Size) {
          ItSets.push_back(std::prev(ItSetDecr.base()));
          ItSetDecr++;
        } else {
          ItSets.push_back(ItSetIncr);
          ItSetIncr++;
        }
      }

      while (ItSetDecr != Blocks.rend()) {
        ItSets.push_back(std::prev(ItSetDecr.base()));
        ItSetDecr++;
      }

      while (ItSetIncr != Blocks.end()) {
        ItSets.push_back(ItSetIncr);
        ItSetIncr++;
      }
    } else {
      ItSetIncr = Blocks.find(BD2.Size);
      if (ItSetIncr != Blocks.end())
        ItSets.push_back(ItSetIncr);
    }

    // Find the closest block starting from blocks with similar size
    std::vector<BlockFingerprint>::iterator BestIt;
    std::map<size_t, std::vector<BlockFingerprint>>::iterator BestSet;
    float BestDist = std::numeric_limits<float>::max();

    for (auto ItSet : ItSets) {
      for (auto BDIt = ItSet->second.begin(), E = ItSet->second.end();
           BDIt != E; BDIt++) {
        auto D = BD2.distance(*BDIt);
        if (D < BestDist) {
          BestDist = D;
          BestIt = BDIt;
          BestSet = ItSet;
          if (BestDist < std::numeric_limits<float>::epsilon())
            break;
        }
      }
      if (BestDist < std::numeric_limits<float>::epsilon())
        break;
    }

    MergeTimers.stop(Timers::Name::codegen_rank);

    // Actually align the chosen blocks
    bool MergedBlock = false;
    if (BestDist < std::numeric_limits<float>::max()) {
      BasicBlock *BB1 = BestIt->BB;
      AlignedCode AlignedBlocks;

      if (EnableNW) {
        SmallVector<Value *, 8> BB1Vec;
        vectorizeBB(BB1Vec, BB1);

        SmallVector<Value *, 8> BB2Vec;
        vectorizeBB(BB2Vec, BB2);

        AlignedBlocks = SA.getAlignment(BB1Vec, BB2Vec);

      } else if (EnablePA) {
        AlignedBlocks = AlignedCode(BB1, BB2);
      }

      if (AlignedBlocks.isProfitable()) {
        AlignedSeq.extend(AlignedBlocks);
        BestSet->second.erase(BestIt);
        MergedBlock = true;
      }
    }

    if (!MergedBlock)
      AlignedSeq.extend(AlignedCode(nullptr, BB2));
  }

  // add this matched pair to the overall sequence
  for (auto &Pair : Blocks)
    for (auto &BD1 : Pair.second)
      AlignedSeq.extend(AlignedCode(BD1.BB, nullptr));

  bool ProfitableFn = AlignedSeq.hasMatches();

  if (Verbose)
    errs() << "RStats: " << NumBB1 << " , " << NumBB2 << "\n";

  if (!ProfitableFn && !ReportStats) {
    if (Verbose)
      errs() << "Skipped: Not profitable enough!!\n";
    return {};
  }

  if (Verbose || ReportStats) {

    unsigned NumMatches = 0;
    unsigned TotalEntries = 0;
    BasicBlock *CurrBB0 = nullptr;
    BasicBlock *CurrBB1 = nullptr;

    for (auto &Entry : AlignedSeq) {
      TotalEntries++;
      if (Entry.match()) {
        NumMatches++;

        if (auto *I = dyn_cast<Instruction>(Entry.get(0)))
          assert(CurrBB0 == I->getParent());
        else
          CurrBB0 = dyn_cast<BasicBlock>(Entry.get(0));

        if (auto *I = dyn_cast<Instruction>(Entry.get(1)))
          assert(CurrBB1 == I->getParent());
        else
          CurrBB1 = dyn_cast<BasicBlock>(Entry.get(1));

        // Always inside a basic block
        assert(CurrBB0 != nullptr);
        assert(CurrBB1 != nullptr);
      }
    }

    errs() << "Matches: " << NumMatches << ", " << TotalEntries << ", "
           << ((double)NumMatches / (double)TotalEntries) << "\n";
  }

  if (Debug)
    AlignedSeq.dump();

  if (ReportStats)
    return {};

  return AlignedSeq;
}

FunctionMergeResult FunctionMerger::merge(Function *F1, Function *F2,
                                          std::string Name) {
  LLVMContext &Context = *ContextPtr;
  FunctionMergeResult ErrorResponse(F1, F2, nullptr);

  if (!validMergePair(F1, F2))
    return ErrorResponse;

  MergeTimers.start(Timers::Name::codegen_align);
  std::optional<AlignedCode> AlignedSeq = align(F1, F2);
  MergeTimers.stop(Timers::Name::codegen_align);

  if (!AlignedSeq)
    return ErrorResponse;

  MergeTimers.start(Timers::Name::codegen_param);

  // Merging parameters
  std::map<unsigned, unsigned> ParamMap1;
  std::map<unsigned, unsigned> ParamMap2;
  std::vector<Type *> Args;

  MergeArguments(Context, F1, F2, AlignedSeq.value(), ParamMap1, ParamMap2,
                 Args);

  Type *RetType1 = F1->getReturnType();
  Type *RetType2 = F2->getReturnType();
  Type *ReturnType = nullptr;

  if (validMergeTypes(F1, F2)) {
    ReturnType = RetType1;
    if (ReturnType->isVoidTy()) {
      ReturnType = RetType2;
    }
  } else {
    MergeTimers.stop(Timers::Name::codegen_param);
    return ErrorResponse;
  }
  FunctionType *FTy =
      FunctionType::get(ReturnType, ArrayRef<Type *>(Args), false);

  if (Name.empty()) {
    Name = "_m_f";
  }
  Function *MergedFunc =
      Function::Create(FTy, // GlobalValue::LinkageTypes::InternalLinkage,
                       GlobalValue::LinkageTypes::PrivateLinkage, Twine(Name),
                       M); // merged.function

  ValueToValueMapTy VMap;

  std::vector<Argument *> ArgsList;
  for (Argument &arg : MergedFunc->args()) {
    ArgsList.push_back(&arg);
  }
  Value *FuncId = ArgsList[0];

  int ArgId = 0;
  for (auto I = F1->arg_begin(), E = F1->arg_end(); I != E; I++) {
    VMap[&(*I)] = ArgsList[ParamMap1[ArgId]];

    ArgId++;
  }

  ArgId = 0;
  for (auto I = F2->arg_begin(), E = F2->arg_end(); I != E; I++) {
    VMap[&(*I)] = ArgsList[ParamMap2[ArgId]];

    ArgId++;
  }

  MergeTimers.stop(Timers::Name::codegen_param);

  SetFunctionAttributes(F1, F2, MergedFunc);

  Value *IsFunc1 = FuncId;

  auto Gen = [&](auto &CG) {
    CG.setFunctionIdentifier(IsFunc1)
        .setEntryPoints(&F1->getEntryBlock(), &F2->getEntryBlock())
        .setReturnTypes(RetType1, RetType2)
        .setMergedFunction(MergedFunc)
        .setMergedEntryPoint(BasicBlock::Create(Context, "entry", MergedFunc))
        .setMergedReturnType(ReturnType)
        .setContext(ContextPtr)
        .setIntPtrType(IntPtrTy);
    if (!CG.generate(AlignedSeq.value(), VMap)) {
      MergedFunc->eraseFromParent();
      MergedFunc = nullptr;
      if (Verbose)
        errs() << "ERROR: Failed to generate the merged function!\n";

      // We might have reached here with the timers still running if generate()
      // returned early
      MergeTimers.force_stop(Timers::Name::codegen_gen);
      MergeTimers.force_stop(Timers::Name::codegen_fix);
    }
  };

  SALSSACodeGen CG(F1, F2);
  Gen(CG);

  FunctionMergeResult Result(F1, F2, MergedFunc);
  Result.setArgumentMapping(F1, ParamMap1);
  Result.setArgumentMapping(F2, ParamMap2);
  Result.setFunctionIdArgument(FuncId != nullptr);
  return Result;
}

void FunctionMerger::replaceByCall(Function *F, FunctionMergeResult &MFR) {
  LLVMContext &Context = M->getContext();

  Value *FuncId = MFR.getFunctionIdValue(F);
  Function *MergedF = MFR.getMergedFunction();

  // Make sure we preserve its linkage
  auto Linkage = F->getLinkage();

  F->deleteBody();
  BasicBlock *NewBB = BasicBlock::Create(Context, "", F);
  IRBuilder<> Builder(NewBB);

  std::vector<Value *> args;
  for (unsigned i = 0; i < MergedF->getFunctionType()->getNumParams(); i++) {
    args.push_back(nullptr);
  }

  if (MFR.hasFunctionIdArgument()) {
    args[0] = FuncId;
  }

  std::vector<Argument *> ArgsList;
  for (Argument &arg : F->args()) {
    ArgsList.push_back(&arg);
  }

  for (auto Pair : MFR.getArgumentMapping(F)) {
    args[Pair.second] = ArgsList[Pair.first];
  }

  for (unsigned i = 0; i < args.size(); i++) {
    if (args[i] == nullptr) {
      args[i] = UndefValue::get(MergedF->getFunctionType()->getParamType(i));
    }
  }

  F->setLinkage(Linkage);

  CallInst *CI =
      (CallInst *)Builder.CreateCall(MergedF, ArrayRef<Value *>(args));
  CI->setTailCall();
  CI->setCallingConv(MergedF->getCallingConv());
  CI->setAttributes(MergedF->getAttributes());
  CI->setIsNoInline();

  if (F->getReturnType()->isVoidTy()) {
    Builder.CreateRetVoid();
  } else {
    Builder.CreateRet(CI);
  }
}

bool FunctionMerger::replaceCallsWith(Function *F, FunctionMergeResult &MFR) {

  Value *FuncId = MFR.getFunctionIdValue(F);
  Function *MergedF = MFR.getMergedFunction();

  unsigned CountUsers = 0;
  std::vector<CallBase *> Calls;
  for (User *U : F->users()) {
    CountUsers++;
    if (auto *CI = dyn_cast<CallInst>(U)) {
      if (CI->getCalledFunction() == F) {
        Calls.push_back(CI);
      }
    } else if (auto *II = dyn_cast<InvokeInst>(U)) {
      if (II->getCalledFunction() == F) {
        Calls.push_back(II);
      }
    }
  }

  if (Calls.size() < CountUsers)
    return false;

  for (CallBase *CI : Calls) {
    IRBuilder<> Builder(CI);

    std::vector<Value *> args;
    for (unsigned i = 0; i < MergedF->getFunctionType()->getNumParams(); i++) {
      args.push_back(nullptr);
    }

    if (MFR.hasFunctionIdArgument()) {
      args[0] = FuncId;
    }

    for (auto Pair : MFR.getArgumentMapping(F)) {
      args[Pair.second] = CI->getArgOperand(Pair.first);
    }

    for (unsigned i = 0; i < args.size(); i++) {
      if (args[i] == nullptr) {
        args[i] = UndefValue::get(MergedF->getFunctionType()->getParamType(i));
      }
    }

    CallBase *NewCB = nullptr;
    if (CI->getOpcode() == Instruction::Call) {
      NewCB = (CallInst *)Builder.CreateCall(MergedF->getFunctionType(),
                                             MergedF, args);
    } else if (CI->getOpcode() == Instruction::Invoke) {
      auto *II = dyn_cast<InvokeInst>(CI);
      NewCB = (InvokeInst *)Builder.CreateInvoke(MergedF->getFunctionType(),
                                                 MergedF, II->getNormalDest(),
                                                 II->getUnwindDest(), args);
    }
    NewCB->setCallingConv(MergedF->getCallingConv());
    NewCB->setAttributes(MergedF->getAttributes());
    NewCB->setIsNoInline();
    Value *CastedV = NewCB;

    if (CI->getNumUses() > 0) {
      CI->replaceAllUsesWith(CastedV);
    }
    CI->eraseFromParent();
  }

  return true;
}

static bool ShouldPreserveGV(const GlobalValue *GV) {
  // Function must be defined here
  if (GV->isDeclaration())
    return true;

  // Available externally is really just a "declaration with a body".
  // if (GV->hasAvailableExternallyLinkage())
  //  return true;

  // Assume that dllexported symbols are referenced elsewhere
  if (GV->hasDLLExportStorageClass())
    return true;

  // Already local, has nothing to do.
  if (GV->hasLocalLinkage())
    return false;

  return false;
}

static int RequiresOriginalInterface(Function *F, FunctionMergeResult &MFR,
                                     StringSet<> &AlwaysPreserved) {
  bool CanErase = !F->hasAddressTaken();
  CanErase =
      CanErase && (AlwaysPreserved.find(F->getName()) == AlwaysPreserved.end());
  if (!HasWholeProgram) {
    CanErase = CanErase && F->isDiscardableIfUnused();
  }
  return !CanErase;
}

static int RequiresOriginalInterfaces(FunctionMergeResult &MFR,
                                      StringSet<> &AlwaysPreserved) {
  auto FPair = MFR.getFunctions();
  Function *F1 = FPair.first;
  Function *F2 = FPair.second;
  return (RequiresOriginalInterface(F1, MFR, AlwaysPreserved) ? 1 : 0) +
         (RequiresOriginalInterface(F2, MFR, AlwaysPreserved) ? 1 : 0);
}

void FunctionMerger::updateCallGraph(Function *F, FunctionMergeResult &MFR,
                                     StringSet<> &AlwaysPreserved) {
  replaceByCall(F, MFR);
  if (!RequiresOriginalInterface(F, MFR, AlwaysPreserved)) {
    bool CanErase = replaceCallsWith(F, MFR);
    CanErase = CanErase && F->use_empty();
    CanErase = CanErase &&
               (AlwaysPreserved.find(F->getName()) == AlwaysPreserved.end());
    if (!HasWholeProgram) {
      CanErase = CanErase && !ShouldPreserveGV(F);
      CanErase = CanErase && F->isDiscardableIfUnused();
    }
    if (CanErase)
      F->eraseFromParent();
  }
}

void FunctionMerger::updateCallGraph(FunctionMergeResult &MFR,
                                     StringSet<> &AlwaysPreserved) {
  auto FPair = MFR.getFunctions();
  Function *F1 = FPair.first;
  Function *F2 = FPair.second;
  updateCallGraph(F1, MFR, AlwaysPreserved);
  updateCallGraph(F2, MFR, AlwaysPreserved);
}

static int EstimateThunkOverhead(FunctionMergeResult &MFR,
                                 StringSet<> &AlwaysPreserved) {
  // return RequiresOriginalInterfaces(MFR, AlwaysPreserved) * 3;
  return RequiresOriginalInterfaces(MFR, AlwaysPreserved) *
         (2 + MFR.getMergedFunction()->getFunctionType()->getNumParams());
}

static size_t EstimateFunctionSize(Function *F, TargetTransformInfo *TTI) {
  float size = 0;
  for (Instruction &I : instructions(F)) {
    switch (I.getOpcode()) {
    // case Instruction::Alloca:
    case Instruction::PHI:
      size += 0.2;
      break;
    // case Instruction::Select:
    //  size += 1.2;
    //  break;
    default:
      auto cost = TTI->getInstructionCost(
          &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
      size += cost.getValue().value();
    }
  }
  return size_t(std::ceil(size));
}

unsigned instToInt(Instruction *I) {
  uint32_t value = 0;
  static uint32_t pseudorand_value = 100;

  if (pseudorand_value > 10000)
    pseudorand_value = 100;

  // std::ofstream myfile;
  // std::string newPath = "/home/sean/similarityChecker.txt";

  // Opcodes must be equivalent for instructions to match -- use opcode value as
  // base
  value = I->getOpcode();

  // Number of operands must be equivalent -- except in the case where the
  // instruction is a return instruction -- +1 to stop being zero
  uint32_t operands =
      I->getOpcode() == Instruction::Ret ? 1 : I->getNumOperands();
  value = value * (operands + 1);

  // Instruction type must be equivalent, pairwise operand types must be
  // equivalent -- use typeID casted to int -- This may not be perfect as my
  // understanding of this is limited
  auto instTypeID = static_cast<uint32_t>(I->getType()->getTypeID());
  value = value * (instTypeID + 1);
  auto *ITypePtr = I->getType();
  if (ITypePtr) {
    value = value * (reinterpret_cast<std::uintptr_t>(ITypePtr) + 1);
  }

  for (size_t i = 0; i < I->getNumOperands(); i++) {
    auto operTypeID =
        static_cast<uint32_t>(I->getOperand(i)->getType()->getTypeID());
    value = value * (operTypeID + 1);

    auto *IOperTypePtr = I->getOperand(i)->getType();

    if (IOperTypePtr) {
      value =
          value *
          (reinterpret_cast<std::uintptr_t>(I->getOperand(i)->getType()) + 1);
    }

    value = value * (i + 1);
  }
  return value;

  // Now for the funky stuff -- this is gonna be a wild ride
  switch (I->getOpcode()) {

  case Instruction::Load: {

    const LoadInst *LI = dyn_cast<LoadInst>(I);
    uint32_t lValue = LI->isVolatile() ? 1 : 10;        // Volatility
    lValue += LI->getAlign().value();                   // Alignment
    lValue += static_cast<unsigned>(LI->getOrdering()); // Ordering

    value = value * lValue;

    break;
  }

  case Instruction::Store: {

    const StoreInst *SI = dyn_cast<StoreInst>(I);
    uint32_t sValue = SI->isVolatile() ? 2 : 20;        // Volatility
    sValue += SI->getAlign().value();                   // Alignment
    sValue += static_cast<unsigned>(SI->getOrdering()); // Ordering

    value = value * sValue;

    break;
  }

  case Instruction::Alloca: {
    const AllocaInst *AI = dyn_cast<AllocaInst>(I);
    uint32_t aValue = AI->getAlign().value(); // Alignment

    if (AI->getArraySize()) {
      aValue += reinterpret_cast<std::uintptr_t>(AI->getArraySize());
    }

    value = value * (aValue + 1);

    break;
  }

  case Instruction::GetElementPtr: // Important
  {

    auto *GEP = dyn_cast<GetElementPtrInst>(I);
    uint32_t gValue = 1;

    SmallVector<Value *, 8> Indices(GEP->idx_begin(), GEP->idx_end());
    gValue = Indices.size() + 1;

    gValue += GEP->isInBounds() ? 3 : 30;

    Type *AggTy = GEP->getSourceElementType();
    gValue += static_cast<unsigned>(AggTy->getTypeID());

    unsigned curIndex = 1;
    for (; curIndex != Indices.size(); ++curIndex) {
      // CompositeType* CTy = dyn_cast<CompositeType>(AggTy);

      if (!AggTy || AggTy->isPointerTy()) {
        if (Deterministic)
          value = pseudorand_value++;
        else
          value = std::rand() % 10000 + 100;
        break;
      }

      Value *Idx = Indices[curIndex];

      if (isa<StructType>(AggTy)) {
        if (!isa<ConstantInt>(Idx)) {
          if (Deterministic)
            value = pseudorand_value++;
          else
            value =
                std::rand() % 10000 + 100; // Use a random number as we don't
                                           // want this to match with anything
          break;
        }

        auto i = 0;
        if (Idx) {
          i = reinterpret_cast<std::uintptr_t>(Idx);
        }
        gValue += i;
      }
    }

    value = value * gValue;

    break;
  }

  case Instruction::Switch: {
    auto *SI = dyn_cast<SwitchInst>(I);
    uint32_t sValue = 1;
    sValue = SI->getNumCases();

    auto CaseIt = SI->case_begin(), CaseEnd = SI->case_end();

    while (CaseIt != CaseEnd) {
      auto *Case = &*CaseIt;
      if (Case) {
        sValue += reinterpret_cast<std::uintptr_t>(Case);
      }
      CaseIt++;
    }

    value = value * sValue;

    break;
  }

  case Instruction::Call: {
    auto *CI = dyn_cast<CallInst>(I);
    uint32_t cValue = 1;

    if (CI->isInlineAsm()) {
      if (Deterministic)
        value = pseudorand_value++;
      else
        value = std::rand() % 10000 + 100;
      break;
    }

    if (CI->getCalledFunction()) {
      cValue = reinterpret_cast<std::uintptr_t>(CI->getCalledFunction());
    }

    if (Function *F = CI->getCalledFunction()) {
      if (auto ID = (Intrinsic::ID)F->getIntrinsicID()) {
        cValue += static_cast<unsigned>(ID);
      }
    }

    cValue += static_cast<unsigned>(CI->getCallingConv());

    value = value * cValue;

    break;
  }

  case Instruction::Invoke: // Need to look at matching landing pads
  {
    auto *II = dyn_cast<InvokeInst>(I);
    uint32_t iValue = 1;

    iValue = static_cast<unsigned>(II->getCallingConv());

    if (II->getAttributes().getRawPointer()) {
      iValue +=
          reinterpret_cast<std::uintptr_t>(II->getAttributes().getRawPointer());
    }

    value = value * iValue;

    break;
  }

  case Instruction::InsertValue: {
    auto *IVI = dyn_cast<InsertValueInst>(I);

    uint32_t ivValue = 1;

    ivValue = IVI->getNumIndices();

    // check element wise equality
    auto Idx = IVI->getIndices();
    const auto *IdxIt = Idx.begin();
    const auto *IdxEnd = Idx.end();

    while (IdxIt != IdxEnd) {
      auto *val = &*IdxIt;
      if (val) {
        ivValue += reinterpret_cast<unsigned>(*val);
      }
      IdxIt++;
    }

    value = value * ivValue;

    break;
  }

  case Instruction::ExtractValue: {
    auto *EVI = dyn_cast<ExtractValueInst>(I);

    uint32_t evValue = 1;

    evValue = EVI->getNumIndices();

    // check element wise equality
    auto Idx = EVI->getIndices();
    const auto *IdxIt = Idx.begin();
    const auto *IdxEnd = Idx.end();

    while (IdxIt != IdxEnd) {
      auto *val = &*IdxIt;
      if (val) {
        evValue += reinterpret_cast<unsigned>(*val);
      }
      IdxIt++;
    }

    value = value * evValue;

    break;
  }

  case Instruction::Fence: {
    auto *FI = dyn_cast<FenceInst>(I);

    uint32_t fValue = 1;

    fValue = static_cast<unsigned>(FI->getOrdering());

    fValue += static_cast<unsigned>(FI->getSyncScopeID());

    value = value * fValue;

    break;
  }

  case Instruction::AtomicCmpXchg: {
    auto *AXI = dyn_cast<AtomicCmpXchgInst>(I);

    uint32_t axValue = 1;

    axValue = AXI->isVolatile() ? 4 : 40;
    axValue += AXI->isWeak() ? 5 : 50;
    axValue += static_cast<unsigned>(AXI->getSuccessOrdering());
    axValue += static_cast<unsigned>(AXI->getFailureOrdering());
    axValue += static_cast<unsigned>(AXI->getSyncScopeID());

    value = value * axValue;

    break;
  }

  case Instruction::AtomicRMW: {
    auto *ARI = dyn_cast<AtomicRMWInst>(I);

    uint32_t arValue = 1;

    arValue = static_cast<unsigned>(ARI->getOperation());
    arValue += ARI->isVolatile() ? 6 : 60;
    arValue += static_cast<unsigned>(ARI->getOrdering());
    arValue += static_cast<unsigned>(ARI->getSyncScopeID());

    value = value * arValue;
    break;
  }

  case Instruction::PHI: {
    if (Deterministic)
      value = pseudorand_value++;
    else
      value = std::rand() % 10000 + 100;
    break;
  }

  default:
    if (auto *CI = dyn_cast<CmpInst>(I)) {
      uint32_t cmpValue = 1;

      cmpValue = static_cast<unsigned>(CI->getPredicate()) + 1;

      value = value * cmpValue;
    }
  }

  // Return
  return value;
}

bool ignoreFunction(Function &F) {
  for (Instruction &I : instructions(F)) {
    if (auto *CB = dyn_cast<CallBase>(&I)) {
      if (Function *F2 = CB->getCalledFunction()) {
        if (auto ID = (Intrinsic::ID)F2->getIntrinsicID()) {
          if (Intrinsic::isOverloaded(ID))
            continue;
          if (Intrinsic::getName(ID).contains("permvar"))
            return true;
          if (Intrinsic::getName(ID).contains("vcvtps"))
            return true;
          if (Intrinsic::getName(ID).contains("avx"))
            return true;
          if (Intrinsic::getName(ID).contains("x86"))
            return true;
          if (Intrinsic::getName(ID).contains("arm"))
            return true;
        }
      }
    }
  }
  return false;
}

bool isMergeable(Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.isVarArg())
    return false;
  if (!HasWholeProgram && F.hasAvailableExternallyLinkage())
    return false;
  if (ignoreFunction(F))
    return false;
  return true;
}

bool FunctionMerging::runImpl(
    Module &M, function_ref<TargetTransformInfo *(Function &)> GTTI) {

  StringSet<> AlwaysPreserved;
  AlwaysPreserved.insert("main");

  srand(time(nullptr));

  if (ReportStats) {
    FunctionMerger FM(&M);
    MatcherReport<Function *> reporter(LSHRows, LSHBands, FM);

    for (auto &F : M)
      if (isMergeable(F))
        reporter.add_candidate(&F);

    reporter.report();
    return false;
  }

  MergeTimers.mergeStart();
  MergeTimers.start(Timers::Name::preprocess);

  FunctionMerger FM(&M);
  std::unique_ptr<Matcher<Function *>> matcher;

  {
    // Check whether to use a linear scan instead
    int size = 0;
    for (auto &F : M)
      if (isMergeable(F))
        size++;

    // Create a threshold based on the application's size
    if (AdaptiveThreshold || AdaptiveBands) {
      double x = std::log10(size) / 10;
      RankingDistance = (double)(x - 0.3);
      if (RankingDistance < 0.05)
        RankingDistance = 0.05;
      if (RankingDistance > 0.4)
        RankingDistance = 0.4;

      if (AdaptiveBands) {
        float target_probability = 0.9;
        float offset = 0.1;
        unsigned tempBands = std::ceil(
            std::log(1.0 - target_probability) /
            std::log(1.0 - std::pow(RankingDistance + offset, LSHRows)));
        if (tempBands < LSHBands)
          LSHBands = tempBands;
      }
      if (AdaptiveThreshold)
        RankingDistance = 1 - RankingDistance;
      else
        RankingDistance = 1.0;
    }

    if (Verbose) {
      errs() << "Threshold: " << RankingDistance << "\n";
      errs() << "LSHRows: " << LSHRows << "\n";
      errs() << "LSHBands: " << LSHBands << "\n";
    }
  }

  if (!ToMergeFile.empty()) {
    matcher = std::make_unique<MatcherManual<Function *>>(FM, ToMergeFile);
    if (Verbose)
      errs() << "Manual Matching\n";
  } else if (EnableF3M) {
    matcher = std::make_unique<MatcherLSH<Function *>>(FM, LSHRows, LSHBands);
    if (Verbose)
      errs() << "LSH MH\n";
  } else {
    matcher = std::make_unique<MatcherFQ<Function *>>(FM);
    if (Verbose)
      errs() << "LIN SCAN FP\n";
  }

  SearchStrategy strategy(LSHRows, LSHBands);
  for (auto &F : M)
    if (isMergeable(F))
      matcher->add_candidate(&F, EstimateFunctionSize(&F, GTTI(F)));

  MergeTimers.stop(Timers::Name::preprocess);

  if (Verbose)
    errs() << "Number of Functions: " << matcher->size() << "\n";
  unsigned TotalMerges = 0;

  while (matcher->size() > 0) {
    MergeTimers.attemptStart();
    MergeTimers.start(Timers::Name::rank);

    Function *F1 = matcher->next_candidate();
    MatchInfo<Function *> match = matcher->get_match(F1);
    matcher->remove_candidate(F1);

    MergeTimers.stop(Timers::Name::rank);
    float OtherDistance = 0.0;

    Function *F2 = match.candidate;
    if (F2 == nullptr) {
      MergeTimers.attemptEnd(false);
      continue;
    }

    MergeTimers.start(Timers::Name::codegen_total);

    std::string F1Name(GetValueName(F1));
    std::string F2Name(GetValueName(F2));

    if (Verbose) {
      if (EnableF3M) {
        Fingerprint<Function *> FP1(F1);
        Fingerprint<Function *> FP2(F2);
        OtherDistance = FP1.distance(FP2);
      } else {
        FingerprintMH<Function *> FP1(F1, strategy);
        FingerprintMH<Function *> FP2(F2, strategy);
        OtherDistance = FP1.distance(FP2);
      }
    }

    if (Verbose)
      errs() << "Attempting: " << F1Name << ", " << F2Name << " : "
             << match.Distance << "\n";

    std::string Name = "_m_f_" + std::to_string(TotalMerges);
    FunctionMergeResult Result = FM.merge(F1, F2, Name);
    MergeTimers.stop(Timers::Name::codegen_total);

    if (Result.getMergedFunction() != nullptr) {
      MergeTimers.start(Timers::Name::verify);
      match.Valid = !verifyFunction(*Result.getMergedFunction());
      MergeTimers.stop(Timers::Name::verify);

      if (Debug) {
        errs() << "F1:\n";
        F1->dump();
        errs() << "F2:\n";
        F2->dump();
        errs() << "F1-F2:\n";
        Result.getMergedFunction()->dump();
      }

      MergeTimers.start(Timers::Name::update);

      if (!match.Valid) {
        Result.getMergedFunction()->eraseFromParent();
      } else {
        size_t MergedSize = EstimateFunctionSize(
            Result.getMergedFunction(), GTTI(*Result.getMergedFunction()));
        size_t Overhead = EstimateThunkOverhead(Result, AlwaysPreserved);

        size_t SizeF12 = MergedSize + Overhead;
        size_t SizeF1F2 = match.OtherSize + match.Size;

        match.MergedSize = SizeF12;
        match.Profitable = (SizeF12 + MergingOverheadThreshold) < SizeF1F2;

        if (!ToMergeFile.empty() || match.Profitable) {
          TotalMerges++;
          matcher->remove_candidate(F2);

          FM.updateCallGraph(Result, AlwaysPreserved);

          if (ReuseMergedFunctions) {
            // feed new function back into the working lists
            matcher->add_candidate(
                Result.getMergedFunction(),
                EstimateFunctionSize(Result.getMergedFunction(),
                                     GTTI(*Result.getMergedFunction())));
          }
        } else {
          Result.getMergedFunction()->eraseFromParent();
        }
      }

      MergeTimers.stop(Timers::Name::update);
    }

    if (Verbose) {
      errs() << F1Name << " + " << F2Name << " <= " << Name
             << " Valid: " << match.Valid << " BinSizes: " << match.OtherSize
             << " + " << match.Size << " <= " << match.MergedSize
             << " IRSizes: " << match.OtherMagnitude << " + " << match.Magnitude
             << " Profitable: " << match.Profitable
             << " Distance: " << match.Distance;
      errs() << " OtherDistance: " << OtherDistance;

      MergeTimers.attemptEnd(true);
    }
  }

  MergeTimers.mergeEnd();
  return true;
}

PreservedAnalyses FunctionMergingPass::run(Module &M,
                                           ModuleAnalysisManager &AM) {
  FunctionMerging FM;
  if (!FM.runImpl(M)) //, GTTI))
    return PreservedAnalyses::all();
  return PreservedAnalyses::none();
}

static std::string GetValueName(const Value *V) {
  if (V) {
    std::string name;
    raw_string_ostream namestream(name);
    V->printAsOperand(namestream, false);
    return namestream.str();
  }
  return "[null]";
}

////////////////////////////////////   SALSSA   ////////////////////////////////

static void postProcessFunction(Function &F) {
  legacy::FunctionPassManager FPM(F.getParent());

  FPM.add(createCFGSimplificationPass());
  FPM.doInitialization();
  FPM.run(F);
  FPM.doFinalization();
}

template <typename BlockListType>
static void CodeGen(BlockListType &Blocks1, BlockListType &Blocks2,
                    BasicBlock *EntryBB1, BasicBlock *EntryBB2,
                    Function *MergedFunc, Value *IsFunc1, BasicBlock *PreBB,
                    AlignedCode &AlignedSeq, ValueToValueMapTy &VMap,
                    std::unordered_map<BasicBlock *, BasicBlock *> &BlocksF1,
                    std::unordered_map<BasicBlock *, BasicBlock *> &BlocksF2,
                    std::unordered_map<Value *, BasicBlock *> &MaterialNodes) {

  auto CloneInst = [](IRBuilder<> &Builder, Function *MF,
                      Instruction *I) -> Instruction * {
    Instruction *NewI = nullptr;
    if (I->getOpcode() == Instruction::Ret) {
      if (MF->getReturnType()->isVoidTy()) {
        NewI = Builder.CreateRetVoid();
      } else {
        NewI = Builder.CreateRet(UndefValue::get(MF->getReturnType()));
      }
    } else {
      // assert(I1->getNumOperands() == I2->getNumOperands() &&
      //      "Num of Operands SHOULD be EQUAL!");
      NewI = I->clone();
      for (unsigned i = 0; i < NewI->getNumOperands(); i++) {
        if (!isa<Constant>(I->getOperand(i)))
          NewI->setOperand(i, nullptr);
      }
      Builder.Insert(NewI);
    }

    // NewI->dropPoisonGeneratingFlags(); //TODO: NOT SURE IF THIS IS VALID

    // TODO: temporarily removing metadata

    SmallVector<std::pair<unsigned, MDNode *>, 8> MDs;
    NewI->getAllMetadata(MDs);
    for (std::pair<unsigned, MDNode *> MDPair : MDs) {
      NewI->setMetadata(MDPair.first, nullptr);
    }

    if (auto *GEP = dyn_cast<GetElementPtrInst>(I)) {
      dyn_cast<GetElementPtrInst>(NewI)->setIsInBounds(GEP->isInBounds());
    }

    /*
    if (auto *CB = dyn_cast<CallBase>(I)) {
      auto *NewCB = dyn_cast<CallBase>(NewI);
      auto AttrList = CB->getAttributes();
      NewCB->setAttributes(AttrList);
    }*/

    return NewI;
  };

  for (auto &Entry : AlignedSeq) {
    if (Entry.match()) {

      auto *I1 = dyn_cast<Instruction>(Entry.get(0));
      auto *I2 = dyn_cast<Instruction>(Entry.get(1));

      std::string BBName =
          (I1 == nullptr) ? "m.label.bb"
                          : (I1->isTerminator() ? "m.term.bb" : "m.inst.bb");

      BasicBlock *MergedBB =
          BasicBlock::Create(MergedFunc->getContext(), BBName, MergedFunc);

      MaterialNodes[Entry.get(0)] = MergedBB;
      MaterialNodes[Entry.get(1)] = MergedBB;

      if (I1 != nullptr && I2 != nullptr) {
        IRBuilder<> Builder(MergedBB);
        Instruction *NewI = CloneInst(Builder, MergedFunc, I1);

        VMap[I1] = NewI;
        VMap[I2] = NewI;
        BlocksF1[MergedBB] = I1->getParent();
        BlocksF2[MergedBB] = I2->getParent();
      } else {
        assert(isa<BasicBlock>(Entry.get(0)) && isa<BasicBlock>(Entry.get(1)) &&
               "Both nodes must be basic blocks!");
        auto *BB1 = dyn_cast<BasicBlock>(Entry.get(0));
        auto *BB2 = dyn_cast<BasicBlock>(Entry.get(1));

        VMap[BB1] = MergedBB;
        VMap[BB2] = MergedBB;
        BlocksF1[MergedBB] = BB1;
        BlocksF2[MergedBB] = BB2;

        // IMPORTANT: make sure any use in a blockaddress constant
        // operation is updated correctly
        for (User *U : BB1->users()) {
          if (auto *BA = dyn_cast<BlockAddress>(U)) {
            VMap[BA] = BlockAddress::get(MergedFunc, MergedBB);
          }
        }
        for (User *U : BB2->users()) {
          if (auto *BA = dyn_cast<BlockAddress>(U)) {
            VMap[BA] = BlockAddress::get(MergedFunc, MergedBB);
          }
        }

        IRBuilder<> Builder(MergedBB);
        for (Instruction &I : *BB1) {
          if (isa<PHINode>(&I)) {
            VMap[&I] = Builder.CreatePHI(I.getType(), 0);
          }
        }
        for (Instruction &I : *BB2) {
          if (isa<PHINode>(&I)) {
            VMap[&I] = Builder.CreatePHI(I.getType(), 0);
          }
        }
      } // end if(instruction)-else
    }
  }

  auto ChainBlocks = [](BasicBlock *SrcBB, BasicBlock *TargetBB,
                        Value *IsFunc1) {
    IRBuilder<> Builder(SrcBB);
    if (SrcBB->getTerminator() == nullptr) {
      Builder.CreateBr(TargetBB);
    } else {
      auto *Br = dyn_cast<BranchInst>(SrcBB->getTerminator());
      assert(Br && Br->isUnconditional() &&
             "Branch should be unconditional at this point!");
      BasicBlock *SuccBB = Br->getSuccessor(0);
      // if (SuccBB != TargetBB) {
      Br->eraseFromParent();
      Builder.CreateCondBr(IsFunc1, SuccBB, TargetBB);
      //}
    }
  };

  auto ProcessEachFunction =
      [&](BlockListType &Blocks,
          std::unordered_map<BasicBlock *, BasicBlock *> &BlocksFX,
          Value *IsFunc1) {
        for (BasicBlock *BB : Blocks) {
          BasicBlock *LastMergedBB = nullptr;
          BasicBlock *NewBB = nullptr;
          bool HasBeenMerged = MaterialNodes.find(BB) != MaterialNodes.end();
          if (HasBeenMerged) {
            LastMergedBB = MaterialNodes[BB];
          } else {
            std::string BBName = std::string("src.bb");
            NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                       MergedFunc);
            VMap[BB] = NewBB;
            BlocksFX[NewBB] = BB;

            // IMPORTANT: make sure any use in a blockaddress constant
            // operation is updated correctly
            for (User *U : BB->users()) {
              if (auto *BA = dyn_cast<BlockAddress>(U)) {
                VMap[BA] = BlockAddress::get(MergedFunc, NewBB);
              }
            }

            // errs() << "NewBB: " << NewBB->getName() << "\n";
            IRBuilder<> Builder(NewBB);
            for (Instruction &I : *BB) {
              if (isa<PHINode>(&I)) {
                VMap[&I] = Builder.CreatePHI(I.getType(), 0);
              }
            }
          }
          for (Instruction &I : *BB) {
            if (isa<LandingPadInst>(&I))
              continue;
            if (isa<PHINode>(&I))
              continue;

            bool HasBeenMerged = MaterialNodes.find(&I) != MaterialNodes.end();
            if (HasBeenMerged) {
              BasicBlock *NodeBB = MaterialNodes[&I];
              if (LastMergedBB) {
                // errs() << "Chaining last merged " << LastMergedBB->getName()
                // << " with " << NodeBB->getName() << "\n";
                ChainBlocks(LastMergedBB, NodeBB, IsFunc1);
              } else {
                IRBuilder<> Builder(NewBB);
                Builder.CreateBr(NodeBB);
                // errs() << "Chaining newBB " << NewBB->getName() << " with "
                // << NodeBB->getName() << "\n";
              }
              // end keep track
              LastMergedBB = NodeBB;
            } else {
              if (LastMergedBB) {
                std::string BBName = std::string("split.bb");
                NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                           MergedFunc);
                ChainBlocks(LastMergedBB, NewBB, IsFunc1);
                BlocksFX[NewBB] = BB;
                // errs() << "Splitting last merged " << LastMergedBB->getName()
                // << " into " << NewBB->getName() << "\n";
              }
              LastMergedBB = nullptr;

              IRBuilder<> Builder(NewBB);
              Instruction *NewI = CloneInst(Builder, MergedFunc, &I);
              VMap[&I] = NewI;
              // errs() << "Cloned into " << NewBB->getName() << " : " <<
              // NewI->getName() << " " << NewI->getOpcodeName() << "\n";
              // I.dump();
            }
          }
        }
      };

  auto ProcessEachFunction_NonSeq =
      [&](int FuncIdx, std::unordered_map<BasicBlock *, BasicBlock *> &BlocksFX,
          Value *IsFunc1) {
        BasicBlock *LastMergedBB = nullptr;
        BasicBlock *NewBB = nullptr;

        for (auto &Entry : AlignedSeq) {
          Value *V = Entry.get(FuncIdx);
          if (V == nullptr)
            continue;

          if (BasicBlock *BB = dyn_cast<BasicBlock>(V)) {
            LastMergedBB = nullptr;
            NewBB = nullptr;
            if (auto It = MaterialNodes.find(BB); It != MaterialNodes.end()) {
              LastMergedBB = It->second;
            } else {
              std::string BBName = std::string("src.bb");
              NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                         MergedFunc);
              VMap[BB] = NewBB;
              BlocksFX[NewBB] = BB;

              // IMPORTANT: make sure any use in a blockaddress constant
              // operation is updated correctly
              for (User *U : BB->users()) {
                if (auto *BA = dyn_cast<BlockAddress>(U)) {
                  VMap[BA] = BlockAddress::get(MergedFunc, NewBB);
                }
              }

              IRBuilder<> Builder(NewBB);
              for (Instruction &I : *BB) {
                if (isa<PHINode>(&I)) {
                  VMap[&I] = Builder.CreatePHI(I.getType(), 0);
                }
              }
            }
          } else if (Instruction *I = dyn_cast<Instruction>(V)) {
            if (isa<LandingPadInst>(I))
              continue;
            if (isa<PHINode>(I))
              continue;

            if (auto It = MaterialNodes.find(I); It != MaterialNodes.end()) {
              BasicBlock *NodeBB = It->second;
              if (LastMergedBB) {
                ChainBlocks(LastMergedBB, NodeBB, IsFunc1);
              } else {
                IRBuilder<> Builder(NewBB);
                Builder.CreateBr(NodeBB);
              }
              // end keep track
              LastMergedBB = NodeBB;
            } else {
              if (LastMergedBB) {
                std::string BBName = std::string("split.bb");
                NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                           MergedFunc);
                ChainBlocks(LastMergedBB, NewBB, IsFunc1);
#ifdef F3M_FIXES
                BlocksFX[NewBB] = BlocksFX[LastMergedBB];
#else
                BlocksFX[NewBB] = BB;
#endif
              }
              LastMergedBB = nullptr;

              IRBuilder<> Builder(NewBB);
              Instruction *NewI = CloneInst(Builder, MergedFunc, I);
              VMap[I] = NewI;
            }
          } else {
            errs() << "Should never get here!\n";
          }
        }
      };

#ifdef CHANGES
  ProcessEachFunction_NonSeq(0, BlocksF1, IsFunc1);
  ProcessEachFunction_NonSeq(1, BlocksF2, IsFunc1);
#else
  ProcessEachFunction(Blocks1, BlocksF1, IsFunc1);
  ProcessEachFunction(Blocks2, BlocksF2, IsFunc1);
#endif

  auto *BB1 = dyn_cast<BasicBlock>(VMap[EntryBB1]);
  auto *BB2 = dyn_cast<BasicBlock>(VMap[EntryBB2]);

  BlocksF1[PreBB] = BB1;
  BlocksF2[PreBB] = BB2;

  if (BB1 == BB2) {
    IRBuilder<> Builder(PreBB);
    Builder.CreateBr(BB1);
  } else {
    IRBuilder<> Builder(PreBB);
    Builder.CreateCondBr(IsFunc1, BB1, BB2);
  }
}

bool FunctionMerger::SALSSACodeGen::generate(AlignedCode &AlignedSeq,
                                             ValueToValueMapTy &VMap) {

  MergeTimers.start(Timers::Name::codegen_gen);

  LLVMContext &Context = CodeGenerator::getContext();
  Function *MergedFunc = CodeGenerator::getMergedFunction();
  Value *IsFunc1 = CodeGenerator::getFunctionIdentifier();
  BasicBlock *EntryBB1 = CodeGenerator::getEntryBlock1();
  BasicBlock *EntryBB2 = CodeGenerator::getEntryBlock2();
  BasicBlock *PreBB = CodeGenerator::getPreBlock();

  std::vector<BasicBlock *> &Blocks1 = CodeGenerator::getBlocks1();
  std::vector<BasicBlock *> &Blocks2 = CodeGenerator::getBlocks2();

  std::list<Instruction *> LinearOffendingInsts;
  std::set<Instruction *> OffendingInsts;
  std::map<Instruction *, std::map<Instruction *, unsigned>>
      CoalescingCandidates;

  std::vector<Instruction *> ListSelects;

  std::vector<AllocaInst *> Allocas;

  // maps new basic blocks in the merged function to their original
  // correspondents
  std::unordered_map<BasicBlock *, BasicBlock *> BlocksF1;
  std::unordered_map<BasicBlock *, BasicBlock *> BlocksF2;
  std::unordered_map<Value *, BasicBlock *> MaterialNodes;

  CodeGen(Blocks1, Blocks2, EntryBB1, EntryBB2, MergedFunc, IsFunc1, PreBB,
          AlignedSeq, VMap, BlocksF1, BlocksF2, MaterialNodes);

  if (Debug)
    errs() << "Assigning label operands\n";

  std::set<BranchInst *> XorBrConds;
  // assigning label operands

  for (auto &Entry : AlignedSeq) {
    Instruction *I1 = nullptr;
    Instruction *I2 = nullptr;

    if (Entry.get(0) != nullptr)
      I1 = dyn_cast<Instruction>(Entry.get(0));
    if (Entry.get(1) != nullptr)
      I2 = dyn_cast<Instruction>(Entry.get(1));

    // Skip non-instructions
    if (I1 == nullptr && I2 == nullptr)
      continue;

    if (Entry.match()) {

      Instruction *I = I1;
      if (I1->getOpcode() == Instruction::Ret) {
        I = (I1->getNumOperands() >= I2->getNumOperands()) ? I1 : I2;
      } else {
        assert(I1->getNumOperands() == I2->getNumOperands() &&
               "Num of Operands SHOULD be EQUAL\n");
      }

      auto *NewI = dyn_cast<Instruction>(VMap[I]);

      for (unsigned i = 0; i < I->getNumOperands(); i++) {
        Value *F1V = nullptr;
        Value *V1 = nullptr;
        if (i < I1->getNumOperands()) {
          F1V = I1->getOperand(i);
          V1 = MapValue(F1V, VMap);
          if (V1 == nullptr) {
            if (Verbose)
              errs() << "ERROR: Null value mapped: V1 = "
                        "MapValue(I1->getOperand(i), "
                        "VMap);\n";
            return false;
          }
        } else {
          V1 = UndefValue::get(I2->getOperand(i)->getType());
        }

        Value *F2V = nullptr;
        Value *V2 = nullptr;
        if (i < I2->getNumOperands()) {
          F2V = I2->getOperand(i);
          V2 = MapValue(F2V, VMap);
          if (V2 == nullptr) {
            if (Verbose)
              errs() << "ERROR: Null value mapped: V2 = "
                        "MapValue(I2->getOperand(i), "
                        "VMap);\n";
            return false;
          }

        } else {
          V2 = UndefValue::get(I1->getOperand(i)->getType());
        }

        assert(V1 != nullptr && "Value should NOT be null!");
        assert(V2 != nullptr && "Value should NOT be null!");

        Value *V = V1; // first assume that V1==V2

        // handling just label operands for now
        if (!isa<BasicBlock>(V))
          continue;

        auto *F1BB = dyn_cast<BasicBlock>(F1V);
        auto *F2BB = dyn_cast<BasicBlock>(F2V);

        if (V1 != V2) {
          auto *BB1 = dyn_cast<BasicBlock>(V1);
          auto *BB2 = dyn_cast<BasicBlock>(V2);

          // auto CacheKey = std::pair<BasicBlock *, BasicBlock *>(BB1, BB2);
          BasicBlock *SelectBB =
              BasicBlock::Create(Context, "bb.select", MergedFunc);
          IRBuilder<> BuilderBB(SelectBB);

          BlocksF1[SelectBB] = I1->getParent();
          BlocksF2[SelectBB] = I2->getParent();

          BuilderBB.CreateCondBr(IsFunc1, BB1, BB2);
          V = SelectBB;
        }

        if (F1BB->isLandingPad() || F2BB->isLandingPad()) {
          LandingPadInst *LP1 = F1BB->getLandingPadInst();
          LandingPadInst *LP2 = F2BB->getLandingPadInst();
          assert((LP1 != nullptr && LP2 != nullptr) &&
                 "Should be both as per the BasicBlock match!");
          (void)LP2;

          BasicBlock *LPadBB =
              BasicBlock::Create(Context, "lpad.bb", MergedFunc);
          IRBuilder<> BuilderBB(LPadBB);

          Instruction *NewLP = LP1->clone();
          BuilderBB.Insert(NewLP);

          BuilderBB.CreateBr(dyn_cast<BasicBlock>(V));

          BlocksF1[LPadBB] = I1->getParent();
          BlocksF2[LPadBB] = I2->getParent();

          VMap[F1BB->getLandingPadInst()] = NewLP;
          VMap[F2BB->getLandingPadInst()] = NewLP;

          V = LPadBB;
        }
        NewI->setOperand(i, V);
      }

    } else { // if(entry.match())-else

      auto AssignLabelOperands =
          [&](Instruction *I,
              std::unordered_map<BasicBlock *, BasicBlock *> &BlocksReMap)
          -> bool {
        auto *NewI = dyn_cast<Instruction>(VMap[I]);
        // if (isa<BranchInst>(I))
        //  errs() << "Setting operand in " << NewI->getParent()->getName() << "
        //  : " << NewI->getName() << " " << NewI->getOpcodeName() << "\n";
        for (unsigned i = 0; i < I->getNumOperands(); i++) {
          // handling just label operands for now
          if (!isa<BasicBlock>(I->getOperand(i)))
            continue;
          auto *FXBB = dyn_cast<BasicBlock>(I->getOperand(i));

          Value *V = MapValue(FXBB, VMap);
          // assert( V!=nullptr && "Mapped value should NOT be NULL!");
          if (V == nullptr)
            return false; // ErrorResponse;

          if (FXBB->isLandingPad()) {

            LandingPadInst *LP = FXBB->getLandingPadInst();
            assert(LP != nullptr && "Should have a landingpad inst!");

            BasicBlock *LPadBB =
                BasicBlock::Create(Context, "lpad.bb", MergedFunc);
            IRBuilder<> BuilderBB(LPadBB);

            Instruction *NewLP = LP->clone();
            BuilderBB.Insert(NewLP);
            VMap[LP] = NewLP;
            BlocksReMap[LPadBB] = I->getParent(); // FXBB;

            BuilderBB.CreateBr(dyn_cast<BasicBlock>(V));

            V = LPadBB;
          }

          NewI->setOperand(i, V);
          // if (isa<BranchInst>(NewI))
          //  errs() << "Operand " << i << ": " << V->getName() << "\n";
        }
        return true;
      };

      if (I1 != nullptr && !AssignLabelOperands(I1, BlocksF1)) {
        if (Verbose)
          errs() << "ERROR: Value should NOT be null\n";

        return false;
      }
      if (I2 != nullptr && !AssignLabelOperands(I2, BlocksF2)) {
        if (Verbose)
          errs() << "ERROR: Value should NOT be null\n";

        return false;
      }
    }
  }

  if (Debug)
    errs() << "Assigning value operands\n";

  auto MergeValues = [&](Value *V1, Value *V2,
                         Instruction *InsertPt) -> Value * {
    if (V1 == V2)
      return V1;

    if (V1 == ConstantInt::getTrue(Context) &&
        V2 == ConstantInt::getFalse(Context))
      return IsFunc1;

    if (V1 == ConstantInt::getFalse(Context) &&
        V2 == ConstantInt::getTrue(Context)) {
      IRBuilder<> Builder(InsertPt);
      /// TODO: create a single not(IsFunc1) for each merged function that needs
      /// it
      return Builder.CreateNot(IsFunc1);
    }

    auto *IV1 = dyn_cast<Instruction>(V1);
    auto *IV2 = dyn_cast<Instruction>(V2);

    if (IV1 && IV2) {
      // if both IV1 and IV2 are non-merged values
      if (BlocksF2.find(IV1->getParent()) == BlocksF2.end() &&
          BlocksF1.find(IV2->getParent()) == BlocksF1.end()) {
        CoalescingCandidates[IV1][IV2]++;
        CoalescingCandidates[IV2][IV1]++;
      }
    }

    IRBuilder<> Builder(InsertPt);
    Instruction *Sel = (Instruction *)Builder.CreateSelect(IsFunc1, V1, V2);
    ListSelects.push_back(dyn_cast<Instruction>(Sel));
    return Sel;
  };

  auto AssignOperands = [&](Instruction *I, bool IsFuncId1) -> bool {
    auto *NewI = dyn_cast<Instruction>(VMap[I]);
    IRBuilder<> Builder(NewI);

    for (unsigned i = 0; i < I->getNumOperands(); i++) {
      if (isa<BasicBlock>(I->getOperand(i)))
        continue;

      Value *V = MapValue(I->getOperand(i), VMap);
      if (V == nullptr)
        return false; // ErrorResponse;

      NewI->setOperand(i, V);
    }

    return true;
  };

  for (auto &Entry : AlignedSeq) {
    Instruction *I1 = nullptr;
    Instruction *I2 = nullptr;

    if (Entry.get(0) != nullptr)
      I1 = dyn_cast<Instruction>(Entry.get(0));
    if (Entry.get(1) != nullptr)
      I2 = dyn_cast<Instruction>(Entry.get(1));

    if (I1 != nullptr && I2 != nullptr) {

      Instruction *I = I1;
      if (I1->getOpcode() == Instruction::Ret) {
        I = (I1->getNumOperands() >= I2->getNumOperands()) ? I1 : I2;
      } else {
        assert(I1->getNumOperands() == I2->getNumOperands() &&
               "Num of Operands SHOULD be EQUAL\n");
      }

      auto *NewI = dyn_cast<Instruction>(VMap[I]);

      IRBuilder<> Builder(NewI);

      if (EnableOperandReordering && isa<BinaryOperator>(NewI) &&
          I->isCommutative()) {

        auto *BO1 = dyn_cast<BinaryOperator>(I1);
        auto *BO2 = dyn_cast<BinaryOperator>(I2);
        Value *VL1 = MapValue(BO1->getOperand(0), VMap);
        Value *VL2 = MapValue(BO2->getOperand(0), VMap);
        Value *VR1 = MapValue(BO1->getOperand(1), VMap);
        Value *VR2 = MapValue(BO2->getOperand(1), VMap);
        if (VL1 == VR2 && VL2 != VR2) {
          std::swap(VL2, VR2);
          // CountOpReorder++;
        } else if (VL2 == VR1 && VL1 != VR1) {
          std::swap(VL1, VR1);
        }

        std::vector<std::pair<Value *, Value *>> Vs;
        Vs.emplace_back(VL1, VL2);
        Vs.emplace_back(VR1, VR2);

        for (unsigned i = 0; i < Vs.size(); i++) {
          Value *V1 = Vs[i].first;
          Value *V2 = Vs[i].second;

          Value *V = MergeValues(V1, V2, NewI);
          if (V == nullptr) {
            if (Verbose) {
              errs() << "Could Not select:\n";
              errs() << "ERROR: Value should NOT be null\n";
            }
            return false; // ErrorResponse;
          }

          NewI->setOperand(i, V);
        }
      } else {
        for (unsigned i = 0; i < I->getNumOperands(); i++) {
          if (isa<BasicBlock>(I->getOperand(i)))
            continue;

          Value *V1 = nullptr;
          if (i < I1->getNumOperands()) {
            V1 = MapValue(I1->getOperand(i), VMap);
            // assert(V1!=nullptr && "Mapped value should NOT be NULL!");
            if (V1 == nullptr) {
              if (Verbose)
                errs() << "ERROR: Null value mapped: V1 = "
                          "MapValue(I1->getOperand(i), "
                          "VMap);\n";
              return false;
            }
          } else {
            V1 = UndefValue::get(I2->getOperand(i)->getType());
          }

          Value *V2 = nullptr;
          if (i < I2->getNumOperands()) {
            V2 = MapValue(I2->getOperand(i), VMap);
            // assert(V2!=nullptr && "Mapped value should NOT be NULL!");

            if (V2 == nullptr) {
              if (Verbose)
                errs() << "ERROR: Null value mapped: V2 = "
                          "MapValue(I2->getOperand(i), "
                          "VMap);\n";
              return false;
            }

          } else {
            V2 = UndefValue::get(I1->getOperand(i)->getType());
          }

          assert(V1 != nullptr && "Value should NOT be null!");
          assert(V2 != nullptr && "Value should NOT be null!");

          Value *V = MergeValues(V1, V2, NewI);
          if (V == nullptr) {
            if (Verbose) {
              errs() << "Could Not select:\n";
              errs() << "ERROR: Value should NOT be null\n";
            }
            return false; // ErrorResponse;
          }

          NewI->setOperand(i, V);

        } // end for operands
      }
    } // end if isomorphic
    else {
      // PDGNode *N = MN->getUniqueNode();
      if (I1 != nullptr && !AssignOperands(I1, true)) {
        if (Verbose)
          errs() << "ERROR: Value should NOT be null\n";
        return false;
      }
      if (I2 != nullptr && !AssignOperands(I2, false)) {
        if (Verbose)
          errs() << "ERROR: Value should NOT be null\n";
        return false;
      }
    } // end 'if-else' non-isomorphic

  } // end for nodes

  if (ListSelects.size() > MaxNumSelection) {
    if (Verbose)
      errs() << "Bailing out: Operand selection threshold\n";
    return false;
  }

  if (Debug)
    errs() << "Assigning PHI operands\n";

  auto AssignPHIOperandsInBlock =
      [&](BasicBlock *BB,
          std::unordered_map<BasicBlock *, BasicBlock *> &BlocksReMap) -> bool {
    for (Instruction &I : *BB) {
      if (auto *PHI = dyn_cast<PHINode>(&I)) {
        auto *NewPHI = dyn_cast<PHINode>(VMap[PHI]);

        std::set<int> FoundIndices;

        for (auto It = pred_begin(NewPHI->getParent()),
                  E = pred_end(NewPHI->getParent());
             It != E; It++) {

          BasicBlock *NewPredBB = *It;

          Value *V = nullptr;

          if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
            int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
            if (Index >= 0) {
              V = MapValue(PHI->getIncomingValue(Index), VMap);
              FoundIndices.insert(Index);
            }
          }

          if (V == nullptr)
            V = UndefValue::get(NewPHI->getType());

          NewPHI->addIncoming(V, NewPredBB);
        }
        if (FoundIndices.size() != PHI->getNumIncomingValues())
          return false;
      }
    }
    return true;
  };

  for (BasicBlock *BB1 : Blocks1) {
    if (!AssignPHIOperandsInBlock(BB1, BlocksF1)) {
      if (Verbose)
        errs() << "ERROR: PHI assignment\n";
      return false;
    }
  }
  for (BasicBlock *BB2 : Blocks2) {
    if (!AssignPHIOperandsInBlock(BB2, BlocksF2)) {
      if (Verbose)
        errs() << "ERROR: PHI assignment\n";
      return false;
    }
  }

#ifdef CHANGES
  // Replace select statements by merged PHIs

  // Collect candidate pairs of PHI Nodes
  SmallSet<std::pair<PHINode *, PHINode *>, 16> CandPHI;
  for (Instruction *I : ListSelects) {
    SelectInst *SI = dyn_cast<SelectInst>(I);
    assert(SI != nullptr);

    PHINode *PT = dyn_cast<PHINode>(SI->getTrueValue());
    PHINode *PF = dyn_cast<PHINode>(SI->getFalseValue());

    if (PT == nullptr || PF == nullptr)
      continue;

    // Only pair PHI Nodes in the same block
    if (PT->getParent() != PF->getParent())
      continue;

    CandPHI.insert({PT, PF});
  }

  SmallSet<PHINode *, 8> RemovedPHIs;
  for (auto [PT, PF] : CandPHI) {
    if ((RemovedPHIs.count(PT) > 0) || (RemovedPHIs.count(PF) > 0))
      continue;
    // Merge PT and PF if:
    // 1) their defined incoming values do not overlap
    // 2) their uses are only select statements on IsFunc1
    bool valid = true;
    SmallVector<SelectInst *> CandSel;

    // Are PHIs mergeable?
    for (unsigned i = 0; i < PT->getNumIncomingValues() && valid; ++i) {
      // if PT incoming value is Undef, this edge pair is mergeable
      Value *VT = PT->getIncomingValue(i);
      if (dyn_cast<UndefValue>(VT) != nullptr)
        continue;

      // if the PF incoming value for the same block is Undef,
      // this edge pair is mergeable
      BasicBlock *PredBB = PT->getIncomingBlock(i);
      if (PF->getBasicBlockIndex(PredBB) < 0) {
        if (Debug) {
          errs() << "PHI ERROR\n";
          PT->dump();
          PF->dump();
          MergedFunc->dump();
        }
      }
      Value *VF = PF->getIncomingValueForBlock(PredBB);
      if (dyn_cast<UndefValue>(VF) != nullptr)
        continue;

      // If the two incoming values are the same, then we can merge them
      if (VT == VF)
        continue;

      valid = false;
    }

    if (!valid)
      continue;

    // Are PHIs only used together in select statements?
    for (auto *UI : PT->users()) {
      SelectInst *SI = dyn_cast<SelectInst>(UI);
      if (SI == nullptr) {
        valid = false;
        break;
      }

      if ((SI->getTrueValue() != PT) || (SI->getFalseValue() != PF)) {
        valid = false;
        break;
      }

      if (SI->getCondition() != IsFunc1) {
        valid = false;
        break;
      }
      CandSel.push_back(SI);
    }

    if (!valid)
      continue;

    // Do the actual PHI merging using PT
    for (unsigned i = 0; i < PT->getNumIncomingValues() && valid; ++i) {
      // If edge is set, use it
      if (dyn_cast<UndefValue>(PT->getIncomingValue(i)) == nullptr)
        continue;

      // If edge not set, copy it from PF
      BasicBlock *PredBB = PT->getIncomingBlock(i);
      PT->setIncomingValue(i, PF->getIncomingValueForBlock(PredBB));
    }

    PF->replaceAllUsesWith(PT);
    PF->eraseFromParent();
    RemovedPHIs.insert(PF);

    // Replace all uses of the select statements with PT
    for (SelectInst *SI : CandSel) {
      SI->replaceAllUsesWith(PT);
      SI->eraseFromParent();
    }
  }
#endif

  if (Debug)
    errs() << "Collecting offending instructions\n";
  DominatorTree DT(*MergedFunc);

  for (Instruction &I : instructions(MergedFunc)) {
    if (auto *PHI = dyn_cast<PHINode>(&I)) {
      for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {

        BasicBlock *BB = PHI->getIncomingBlock(i);
        if (BB == nullptr) {
          if (Verbose)
            errs() << "ERROR: Null incoming block\n";
          return false;
        }

        Value *V = PHI->getIncomingValue(i);
        if (V == nullptr) {
          if (Verbose)
            errs() << "ERROR: Null incoming value\n";
          return false;
        }

        if (auto *IV = dyn_cast<Instruction>(V)) {
          if (BB->getTerminator() == nullptr) {
            if (Verbose)
              errs() << "ERROR: Null terminator\n";
            return false;
          }

          if (!DT.dominates(IV, BB->getTerminator())) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    } else {
      for (unsigned i = 0; i < I.getNumOperands(); i++) {
        if (I.getOperand(i) == nullptr) {
          if (Verbose)
            errs() << "ERROR: Null operand\n";
          if (Debug) {
            MergedFunc->dump();
            I.getParent()->dump();
            I.dump();
          }
          return false;
        }

        if (auto *IV = dyn_cast<Instruction>(I.getOperand(i))) {
          if (!DT.dominates(IV, &I)) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    }
  }

  for (BranchInst *NewBr : XorBrConds) {
    IRBuilder<> Builder(NewBr);
    Value *XorCond = Builder.CreateXor(NewBr->getCondition(), IsFunc1);
    NewBr->setCondition(XorCond);
  }

  MergeTimers.stop(Timers::Name::codegen_gen);
  MergeTimers.start(Timers::Name::codegen_fix);

  auto StoreInstIntoAddr = [](Instruction *IV, Value *Addr) {
    IRBuilder<> Builder(IV->getParent());
    if (IV->isTerminator()) {
      BasicBlock *SrcBB = IV->getParent();
      if (auto *II = dyn_cast<InvokeInst>(IV)) {
        BasicBlock *DestBB = II->getNormalDest();

        Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
        // create PHI
        PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
        for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
             PredIt != PredE; PredIt++) {
          BasicBlock *PredBB = *PredIt;
          if (PredBB == SrcBB) {
            PHI->addIncoming(IV, PredBB);
          } else {
            PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
          }
        }
        Builder.CreateStore(PHI, Addr);
      } else {
        for (auto SuccIt = succ_begin(SrcBB), SuccE = succ_end(SrcBB);
             SuccIt != SuccE; SuccIt++) {
          BasicBlock *DestBB = *SuccIt;

          Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
          // create PHI
          PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
          for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
               PredIt != PredE; PredIt++) {
            BasicBlock *PredBB = *PredIt;
            if (PredBB == SrcBB) {
              PHI->addIncoming(IV, PredBB);
            } else {
              PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
            }
          }
          Builder.CreateStore(PHI, Addr);
        }
      }
    } else {
      Instruction *LastI = nullptr;
      Instruction *InsertPt = nullptr;
      for (Instruction &I : *IV->getParent()) {
        InsertPt = &I;
        if (LastI == IV)
          break;
        LastI = &I;
      }
      if (isa<PHINode>(InsertPt) || isa<LandingPadInst>(InsertPt)) {
        Builder.SetInsertPoint(&*IV->getParent()->getFirstInsertionPt());
        // Builder.SetInsertPoint(IV->getParent()->getTerminator());
      } else
        Builder.SetInsertPoint(InsertPt);

      Builder.CreateStore(IV, Addr);
    }
  };

  auto MemfyInst = [&](std::set<Instruction *> &InstSet) -> AllocaInst * {
    if (InstSet.empty())
      return nullptr;
    IRBuilder<> Builder(&*PreBB->getFirstInsertionPt());
    AllocaInst *Addr = Builder.CreateAlloca((*InstSet.begin())->getType());
    Type *Ty = Addr->getAllocatedType();

    for (Instruction *I : InstSet) {
      for (auto UIt = I->use_begin(), E = I->use_end(); UIt != E;) {
        Use &UI = *UIt;
        UIt++;

        auto *User = cast<Instruction>(UI.getUser());

        if (auto *PHI = dyn_cast<PHINode>(User)) {
          /// TODO: make sure getOperandNo is getting the correct incoming edge
          auto InsertionPt =
              PHI->getIncomingBlock(UI.getOperandNo())->getTerminator();
          /// TODO: If the terminator of the incoming block is the producer of
          //        the value we want to store, the load cannot be inserted
          //        between the producer and the user. Something more complex is
          //        needed.
          if (InsertionPt == I)
            continue;
          IRBuilder<> Builder(InsertionPt);
          UI.set(Builder.CreateLoad(Ty, Addr));
        } else {
          IRBuilder<> Builder(User);
          UI.set(Builder.CreateLoad(Ty, Addr));
        }
      }
    }

    for (Instruction *I : InstSet)
      StoreInstIntoAddr(I, Addr);

    return Addr;
  };

  auto isCoalescingProfitable = [&](Instruction *I1, Instruction *I2) -> bool {
    std::set<BasicBlock *> BBSet1;
    std::set<BasicBlock *> UnionBB;
    for (User *U : I1->users()) {
      if (auto *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB1 = UI->getParent();
        BBSet1.insert(BB1);
        UnionBB.insert(BB1);
      }
    }

    unsigned Intersection = 0;
    for (User *U : I2->users()) {
      if (auto *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB2 = UI->getParent();
        UnionBB.insert(BB2);
        if (BBSet1.find(BB2) != BBSet1.end())
          Intersection++;
      }
    }

    const float Threshold = 0.7;
    return (float(Intersection) / float(UnionBB.size()) > Threshold);
  };

  auto OptimizeCoalescing =
      [&](Instruction *I, std::set<Instruction *> &InstSet,
          std::map<Instruction *, std::map<Instruction *, unsigned>>
              &CoalescingCandidates,
          std::set<Instruction *> &Visited) {
        Instruction *OtherI = nullptr;
        unsigned Score = 0;
        if (CoalescingCandidates.find(I) != CoalescingCandidates.end()) {
          for (auto &Pair : CoalescingCandidates[I]) {
            if (Pair.second > Score &&
                Visited.find(Pair.first) == Visited.end()) {
              if (isCoalescingProfitable(I, Pair.first)) {
                OtherI = Pair.first;
                Score = Pair.second;
              }
            }
          }
        }
        /*
        if (OtherI==nullptr) {
          for (Instruction *OI : OffendingInsts) {
            if (OI->getType()!=I->getType()) continue;
            if (Visited.find(OI)!=Visited.end()) continue;
            if (CoalescingCandidates.find(OI)!=CoalescingCandidates.end())
        continue; if( (BlocksF2.find(I->getParent())==BlocksF2.end() &&
        BlocksF1.find(OI->getParent())==BlocksF1.end()) ||
                (BlocksF2.find(OI->getParent())==BlocksF2.end() &&
        BlocksF1.find(I->getParent())==BlocksF1.end()) ) { OtherI = OI; break;
            }
          }
        }
        */
        if (OtherI) {
          InstSet.insert(OtherI);
          // errs() << "Coalescing: " << GetValueName(I->getParent()) << ":";
          // I->dump(); errs() << "With: " << GetValueName(OtherI->getParent())
          // << ":"; OtherI->dump();
        }
      };

  if (Debug)
    errs() << "Finishing code\n";

  if (MergedFunc != nullptr) {
    // errs() << "Offending: " << OffendingInsts.size() << " ";
    // errs() << ((float)OffendingInsts.size())/((float)AlignedSeq.size()) << "
    // : "; if (OffendingInsts.size()>1000) { if (false) {
    if (((float)OffendingInsts.size()) / ((float)AlignedSeq.size()) > 4.5) {
      if (Debug)
        errs() << "Bailing out\n";
      return false;
    }

    if (Debug)
      errs() << "Fixing Domination:\n";

    std::set<Instruction *> Visited;
    for (Instruction *I : LinearOffendingInsts) {
      if (Visited.find(I) != Visited.end())
        continue;

      std::set<Instruction *> InstSet;
      InstSet.insert(I);

      // Create a coalescing group in InstSet
      if (EnableSALSSACoalescing)
        OptimizeCoalescing(I, InstSet, CoalescingCandidates, Visited);

      for (Instruction *OtherI : InstSet)
        Visited.insert(OtherI);

      AllocaInst *Addr = MemfyInst(InstSet);
      if (Addr)
        Allocas.push_back(Addr);
    }

    if (Debug)
      errs() << "Fixed Domination:\n";

    DominatorTree DT(*MergedFunc);
    PromoteMemToReg(Allocas, DT, nullptr);

    if (Debug)
      errs() << "Mem2Reg:\n";

    if (verifyFunction(*MergedFunc)) {
      if (Verbose)
        errs() << "ERROR: Produced Broken Function!\n";
      return false;
    }
    MergeTimers.stop(Timers::Name::codegen_fix);
    MergeTimers.start(Timers::Name::codegen_postopt);
    postProcessFunction(*MergedFunc);
    MergeTimers.stop(Timers::Name::codegen_postopt);
  }
  return MergedFunc != nullptr;
}
