/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <set>
#include <vector>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();
  const DataLayout &DL = M.getDataLayout();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLUCPtr =
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_uc_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) break;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /*
   * This is added to store xor distance
   * of covered and uncovered branches
   * */
  std::set<u32> Visited;

  auto IntptrTy = Type::getIntNTy(C, DL.getPointerSizeInBits());
  auto Strcmp = M.getOrInsertFunction("__afl_strcmp", Int32Ty, IntptrTy, IntptrTy);
  auto Strncmp = M.getOrInsertFunction("__afl_strncmp", Int32Ty, IntptrTy, IntptrTy, Int32Ty);

  for (auto &F: M)
    for (auto &BB: F) {
      auto T = BB.getTerminator();
      if (T->getNumSuccessors() >= 2) {
        u32 CurId = 0, NextId = 0;
        BasicBlock::iterator IP = --BB.end();
        IRBuilder<> IRB(&(*IP));
        for (auto &Inst : BB) {
          if (BinaryOperator* OP = dyn_cast<BinaryOperator>(&Inst)) {
            if (strcmp(OP->getOpcodeName(), "xor") == 0) {
              Value* A1 = OP->getOperand(1);
              CurId = dyn_cast<ConstantInt>(A1)->getZExtValue();
              break;
            }
          }
        }

        if (Visited.count(CurId) > 0) break;
        Visited.insert(CurId);

        std::vector<Value*> XorDists;
        auto It = --BB.end();

        /* Last instruction of block */
        if (SwitchInst* SI = dyn_cast<SwitchInst>(&(*It))) {
          Value* A0 = SI->getCondition();
          XorDists.push_back(ConstantInt::get(Int32Ty, 1));
          for (auto Case : SI->cases()) {
            Value* A1 = Case.getCaseValue();
            Value* A2 = IRB.CreateXor(A0, A1);
            XorDists.push_back(A2);
          }
        }

        if (BranchInst* BR = dyn_cast<BranchInst>(&(*It))) {
          Value *A0 = BR->getCondition();
          Instruction *Inst = NULL;

          if (
            (Inst = dyn_cast<ICmpInst>(A0)) || 
            (Inst = dyn_cast<BinaryOperator>(A0)) ||
            (
             (Inst = dyn_cast<SelectInst>(A0)) && 
             (Inst = dyn_cast<ICmpInst>(Inst->getOperand(0)))
            )
          ) {
            std::vector<Value*> tmps;
            for (auto Idx = 0; Idx < 2; Idx += 1) {
              Value* A0 = Inst->getOperand(Idx);
              if (CallInst *CALL = dyn_cast<CallInst>(A0)) {
                if (Function* Func = CALL->getCalledFunction()) {
                  if (Func->getName() == "strcmp" || Func->getName() == "strncmp") {
                    A0 = IRB.CreateXor(
                      IRB.CreateZExt(CALL->getArgOperand(0), IRB.getInt64Ty()),
                      IRB.CreateZExt(CALL->getArgOperand(1), IRB.getInt64Ty())
                    );
                  }
                }
              }
              tmps.push_back(A0);
            }
            Value* A0 = IRB.CreateXor(tmps[0], tmps[1]);
            XorDists.push_back(A0);
            XorDists.push_back(A0);
          } else if ((Inst = dyn_cast<FCmpInst>(A0))) {
            Inst = dyn_cast<FCmpInst>(A0);
            Value* A0 = Inst->getOperand(0);
            Value* A1 = Inst->getOperand(1);
            A0 = IRB.CreateFPToSI(A0, IRB.getInt64Ty());
            A1 = IRB.CreateFPToSI(A1, IRB.getInt64Ty());
            A0 = IRB.CreateXor(A0, A1);
            XorDists.push_back(A0);
            XorDists.push_back(A0);
          } else {
            // TODO: phi node
            errs() << "[LOG] "<< *A0 << "\n";
          }
        }

        // Fallback
        if (XorDists.size() != T->getNumSuccessors()) continue;

        LoadInst *UCPtr = NULL;
        Value *PrevLocCasted = NULL;
        for (auto Idx = 0; Idx < T->getNumSuccessors(); Idx += 1) {
          auto Suc = T->getSuccessor(Idx);
          for (auto &Inst : *Suc) {
            if (BinaryOperator* OP = dyn_cast<BinaryOperator>(&Inst)) {
              if (strcmp(OP->getOpcodeName(), "xor") == 0) {
                Value* A1 = OP->getOperand(1);
                NextId = dyn_cast<ConstantInt>(A1)->getZExtValue();
                break;
              }
            }
          }
          if (CurId && NextId) {
            // A block can jump to another block and jump back through call instruction.
            // Thefore, we load AFLPrevLoc instead of using CurId
            if (PrevLocCasted == NULL) {
              LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
              PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
              PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());
            }
            auto CurLoc = IRB.CreateXor(PrevLocCasted, ConstantInt::get(Int32Ty, NextId));
            if (UCPtr == NULL) {
              UCPtr = IRB.CreateLoad(AFLUCPtr);
              UCPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            }
            Value *UCPtrIdx = IRB.CreateGEP(UCPtr, CurLoc);
            IRB.CreateStore(XorDists[Idx], UCPtrIdx)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          }
        }
      }
    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
