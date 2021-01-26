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
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

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

  Type *VoidTy = Type::getVoidTy(C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

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

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Open file to read id */

  u32 CurId = 0;
  s32 Fd  = open("/tmp/.cur_id", O_RDWR | O_CREAT, 0600);;
  if (Fd < 0) PFATAL("Unable to create /tmp/.cur_id");
  if (read(Fd, &CurId, 4) < 4) PFATAL("Short read /tmp/.cur_id");

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, Int32Ty);

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

      /* TODO */
      CurId += 1;

      if (BB.size() > 2) {
        auto It = BB.end();
        u32 IsConditionalBr = 0;
        --It;
        if (BranchInst* BR = dyn_cast<BranchInst>(&(*It))) {
          IsConditionalBr = BR->isConditional();
        }
        if (SwitchInst* SI = dyn_cast<SwitchInst>(&(*It))) {
          IRBuilder<> IRB(&(*SI));
          FunctionCallee Insert = M.getOrInsertFunction("insert_distance", VoidTy, Int32Ty, Int32Ty, Int32Ty);
          Value *Cond = SI->getCondition();
          if (Cond->getType()->getScalarSizeInBits() <= Int64Ty->getScalarSizeInBits()) {
            /* Convert label to Index */
            u32 NumCases = SI->getNumCases() + 1;
            u32 Labels[NumCases];
            u32 CurLabel = 1;
            memset(Labels , 0, sizeof(u32) * NumCases);
            for (u32 I = 0; I < NumCases; I += 1) {
              u32 Updated = false;
              for (u32 J = 0; J < NumCases; J += 1) {
                Value* A0 = SI->getOperand(1 + 2 * I);
                Value* A1 = SI->getOperand(1 + 2 * J);
                if (A0 == A1 && !Labels[J]) {
                  Labels[J] = CurLabel;
                  Updated = true;
                }
              }
              if (Updated) CurLabel += 1;
            }
            /* Save distance */
            Value* DefaultDis = ConstantInt::get(Int32Ty, 0);
            u32 Inc = 0;
            for (auto It : SI->cases()) {
              Constant *CaseVal = It.getCaseValue();
              Value* Distance = IRB.CreateXor(Cond, CaseVal);
              Distance = IRB.CreateIntCast(Distance, Int32Ty, false);
              Value* Case = ConstantInt::get(Int32Ty, Labels[Inc + 1]);
              IRB.CreateCall(Insert, { ConstantInt::get(Int32Ty, CurId), Case, Distance });
              Value* NotCovered = IRB.CreateICmpNE(Distance, ConstantInt::get(Int32Ty, 0));
              DefaultDis = IRB.CreateAdd(DefaultDis, NotCovered);
              Inc += 1;
            }
            DefaultDis = IRB.CreateSub(ConstantInt::get(Int32Ty, SI->getNumCases()), DefaultDis);
            Value* Case = ConstantInt::get(Int32Ty, Labels[0]);
            IRB.CreateCall(Insert, { ConstantInt::get(Int32Ty, CurId), Case, DefaultDis });
          }
        }
        --It;
        if (ICmpInst *ICMP = dyn_cast<ICmpInst>(&(*It))) {
          if (IsConditionalBr) {
            IRBuilder<> IRB(&(*ICMP));
            Value* A0 = ICMP->getOperand(0);
            Value* A1 = ICMP->getOperand(1);
            if (A0->getType()->isIntegerTy()) {
              if (A0->getType()->getScalarSizeInBits() <= Int64Ty->getScalarSizeInBits()) {
                Value* Distance = IRB.CreateXor(A0, A1);
                Distance = IRB.CreateIntCast(Distance, Int32Ty, false);
                FunctionCallee Insert = M.getOrInsertFunction("insert_distance", VoidTy, Int32Ty, Int32Ty, Int32Ty);
                Value* Zero = ConstantInt::get(Int32Ty, 0);
                IRB.CreateCall(Insert, { ConstantInt::get(Int32Ty, CurId), Zero, Distance });
              }
            }
          }
        }
      }

      FunctionCallee Insert = M.getOrInsertFunction("insert_block", VoidTy, Int32Ty);
      IRB.CreateCall(Insert, { ConstantInt::get(Int32Ty, CurId) });
      // errs() << BB;
    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  lseek(Fd, 0, SEEK_SET);
  if (write(Fd, &CurId, 4) < 4) PFATAL("Short write .cur_id");
  close(Fd);

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
