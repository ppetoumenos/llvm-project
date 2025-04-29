//===- FunctionMerging.h - A function merging pass ----------------------===//
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
// Function Merging by Sequence Alignment: An Interprocedural Code-Size
// Optimization
// Rodrigo C. O. Rocha, Pavlos Petoumenos, Zheng Wang, Murray Cole, Hugh Leather
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_IPO_FUNCTIONMERGING_H
#define LLVM_TRANSFORMS_IPO_FUNCTIONMERGING_H

#include "llvm/ADT/SequenceAlignment.h"
#include "llvm/ADT/SANeedlemanWunsch.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSet.h"

#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"

#include "llvm/InitializePasses.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Transforms/IPO/SearchStrategy.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <map>
#include <vector>

namespace llvm {

class AlignedCode : public AlignedSequence<Value *> {
public:
  int Insts{0};
  int Matches{0};
  int CoreMatches{0};

  AlignedCode() = default;

  AlignedCode(const AlignedCode &Other)
      : AlignedSequence(Other), Insts{Other.Insts}, Matches{Other.Matches},
        CoreMatches{Other.CoreMatches} {}

  AlignedCode(AlignedCode &&Other)
      : AlignedSequence(Other), Insts{Other.Insts}, Matches{Other.Matches},
        CoreMatches{Other.CoreMatches} {}

  AlignedCode(const AlignedSequence<Value *> &Other) : AlignedSequence(Other) {}

  AlignedCode(AlignedSequence<Value *> &&Other) : AlignedSequence(Other) {}

  AlignedCode(BasicBlock *B1, BasicBlock *B2);

  AlignedCode &operator=(const AlignedCode &Other) {
    Data = Other.Data;
    LargestMatch = Other.LargestMatch;
    Insts = Other.Insts;
    Matches = Other.Matches;
    CoreMatches = Other.CoreMatches;
    return (*this);
  }

  void extend(const AlignedCode &Other);
  void extend(int index, const BasicBlock *BB);

  bool hasMatches() const { return (Matches == Insts) || (CoreMatches > 0); };
  bool isProfitable() const;

  void dump() const;
};

class FunctionMergeResult {
private:
  Function *F1;
  Function *F2;
  Function *MergedFunction;
  bool HasIdArg;
  std::map<unsigned, unsigned> ParamMap1;
  std::map<unsigned, unsigned> ParamMap2;

  FunctionMergeResult()
      : F1(nullptr), F2(nullptr), MergedFunction(nullptr), HasIdArg(false) {}

public:
  FunctionMergeResult(Function *F1, Function *F2, Function *MergedFunction)
      : F1(F1), F2(F2), MergedFunction(MergedFunction), HasIdArg(true) {}

  std::pair<Function *, Function *> getFunctions() {
    return std::pair<Function *, Function *>(F1, F2);
  }

  std::map<unsigned, unsigned> &getArgumentMapping(Function *F) {
    return (F1 == F) ? ParamMap1 : ParamMap2;
  }

  Value *getFunctionIdValue(Function *F) {
    if (F == F1)
      return ConstantInt::getTrue(IntegerType::get(F1->getContext(), 1));
    if (F == F2)
      return ConstantInt::getFalse(IntegerType::get(F2->getContext(), 1));
    return nullptr;
  }

  void setFunctionIdArgument(bool HasFuncIdArg) { HasIdArg = HasFuncIdArg; }

  bool hasFunctionIdArgument() { return HasIdArg; }

  // returns whether or not the merge operation was successful
  operator bool() const { return (MergedFunction != nullptr); }

  void setArgumentMapping(Function *F, std::map<unsigned, unsigned> &ParamMap) {
    if (F == F1)
      ParamMap1 = ParamMap;
    else if (F == F2)
      ParamMap2 = ParamMap;
  }

  void addArgumentMapping(Function *F, unsigned SrcArg, unsigned DstArg) {
    if (F == F1)
      ParamMap1[SrcArg] = DstArg;
    else if (F == F2)
      ParamMap2[SrcArg] = DstArg;
  }

  Function *getMergedFunction() { return MergedFunction; }
};

class FunctionMerger {
private:
  Module *M;

  function_ref<BlockFrequencyInfo *(Function &)> LookupBFI;

  Type *IntPtrTy;

  const DataLayout *DL;
  LLVMContext *ContextPtr;

  void replaceByCall(Function *F, FunctionMergeResult &MergedFunc);
  bool replaceCallsWith(Function *F, FunctionMergeResult &MergedFunc);

  void updateCallGraph(Function *F, FunctionMergeResult &MFR,
                       StringSet<> &AlwaysPreserved);

public:
  FunctionMerger(Module *M) : M(M), IntPtrTy(nullptr) {
    if (M) {
      DL = &M->getDataLayout();
      ContextPtr = &M->getContext();
      IntPtrTy = DL->getIntPtrType(*ContextPtr);
    }
  }

  bool validMergeTypes(Function *F1, Function *F2);
  static bool areTypesEquivalent(Type *Ty1, Type *Ty2, const DataLayout *DL);

  static bool match(Value *V1, Value *V2);
  static bool matchInstructions(Instruction *I1, Instruction *I2);
  static bool matchWholeBlocks(Value *V1, Value *V2);
  static bool matchBlocks(BasicBlock *B1, BasicBlock *B2);

  void updateCallGraph(FunctionMergeResult &Result,
                       StringSet<> &AlwaysPreserved);

  std::optional<AlignedCode> align(Function *F1, Function *F2);
  FunctionMergeResult merge(Function *F1, Function *F2, std::string Name = "");

  class CodeGenerator {
  private:
    LLVMContext *ContextPtr;
    Type *IntPtrTy;

    Value *IsFunc1;

    std::vector<BasicBlock *> Blocks1;
    std::vector<BasicBlock *> Blocks2;

    BasicBlock *EntryBB1;
    BasicBlock *EntryBB2;
    BasicBlock *PreBB;

    Type *RetType1;
    Type *RetType2;
    Type *ReturnType;

    Function *MergedFunc;

  public:
    CodeGenerator(Function *F1, Function *F2) {
      for (BasicBlock &BB : *F1)
        Blocks1.push_back(&BB);
      for (BasicBlock &BB : *F2)
        Blocks2.push_back(&BB);
    }
    virtual ~CodeGenerator() = default;

    CodeGenerator &setContext(LLVMContext *ContextPtr) {
      this->ContextPtr = ContextPtr;
      return *this;
    }

    CodeGenerator &setIntPtrType(Type *IntPtrTy) {
      this->IntPtrTy = IntPtrTy;
      return *this;
    }

    CodeGenerator &setFunctionIdentifier(Value *IsFunc1) {
      this->IsFunc1 = IsFunc1;
      return *this;
    }

    CodeGenerator &setEntryPoints(BasicBlock *EntryBB1, BasicBlock *EntryBB2) {
      this->EntryBB1 = EntryBB1;
      this->EntryBB2 = EntryBB2;
      return *this;
    }

    CodeGenerator &setReturnTypes(Type *RetType1, Type *RetType2) {
      this->RetType1 = RetType1;
      this->RetType2 = RetType2;
      return *this;
    }

    CodeGenerator &setMergedEntryPoint(BasicBlock *PreBB) {
      this->PreBB = PreBB;
      return *this;
    }

    CodeGenerator &setMergedReturnType(Type *ReturnType) {
      this->ReturnType = ReturnType;
      return *this;
    }

    CodeGenerator &setMergedFunction(Function *MergedFunc) {
      this->MergedFunc = MergedFunc;
      return *this;
    }

    Function *getMergedFunction() { return MergedFunc; }
    Type *getMergedReturnType() { return ReturnType; }

    Value *getFunctionIdentifier() { return IsFunc1; }

    LLVMContext &getContext() { return *ContextPtr; }

    std::vector<BasicBlock *> &getBlocks1() { return Blocks1; }
    std::vector<BasicBlock *> &getBlocks2() { return Blocks2; }

    BasicBlock *getEntryBlock1() { return EntryBB1; }
    BasicBlock *getEntryBlock2() { return EntryBB2; }
    BasicBlock *getPreBlock() { return PreBB; }

    Type *getReturnType1() { return RetType1; }
    Type *getReturnType2() { return RetType2; }

    Type *getIntPtrType() { return IntPtrTy; }

    virtual bool generate(AlignedCode &AlignedSeq, ValueToValueMapTy &VMap) = 0;
  };

  class SALSSACodeGen : public FunctionMerger::CodeGenerator {

  public:
    SALSSACodeGen(Function *F1, Function *F2) : CodeGenerator(F1, F2) {}
    virtual ~SALSSACodeGen() = default;
    virtual bool generate(AlignedCode &AlignedSeq,
                          ValueToValueMapTy &VMap) override;
  };
};

FunctionMergeResult MergeFunctions(Function *F1, Function *F2);

class FunctionMergingPass : public PassInfoMixin<FunctionMergingPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm
#endif
