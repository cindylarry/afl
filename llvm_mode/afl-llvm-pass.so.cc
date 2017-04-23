/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#define AFL_LOG_BASIC_BLOCKS

using namespace llvm;

namespace {
  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      /// make sure that we only seed once
      bool seeded = false;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };
}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {
  if(!seeded) {
    char* random_seed_str = getenv("AFL_RANDOM_SEED");
    if(random_seed_str != NULL) {
      unsigned int seed;
      sscanf(random_seed_str, "%u", &seed);
      srandom(seed);
      //SAYF("seeded with %u\n", seed);
      seeded = true;
    }
  }

  const bool just_annotate = (getenv("AFL_JUST_ANNOTATE") != NULL);

  LLVMContext &C = M.getContext();

  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
#ifdef AFL_LOG_BASIC_BLOCKS
  IntegerType *Int16Ty = IntegerType::getInt16Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
#else
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
#endif

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

#ifdef AFL_LOG_BASIC_BLOCKS
  assert(MAP_SIZE <= MAP_SIZE);
  GlobalVariable *AFLIdPtr =
      new GlobalVariable(M, PointerType::get(Int16Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_id_ptr");
#else
  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);
#endif

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = R(MAP_SIZE);

#ifdef AFL_LOG_BASIC_BLOCKS
      ConstantInt *CurLoc = ConstantInt::get(Int16Ty, cur_loc);
#else
      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
#endif

      if(just_annotate) {
        auto meta_loc = MDNode::get(C, ConstantAsMetadata::get(CurLoc));
        BB.getInstList().begin()->setMetadata("afl_cur_loc", meta_loc);
        BB.getTerminator()->setMetadata("afl_cur_loc", meta_loc);
      } else {

#ifdef AFL_LOG_BASIC_BLOCKS
        // this instrumentation logs the basic block ids (cur_loc) to an array
        //   %2 = load i32*, i32** @id_ptr, align 8, !tbaa !1
        //   store i32 %0, i32* %2, align 4, !tbaa !5
        //   %3 = getelementptr inbounds i32, i32* %2, i64 1
        //   store i32* %3, i32** @id_ptr, align 8, !tbaa !1

        // load id_ptr
        LoadInst* IdPtr = IRB.CreateLoad(AFLIdPtr);
        IdPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        // store id
        IRB.CreateStore(CurLoc, IdPtr)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        // increment id_ptr
        Value* NewIdPtr = IRB.CreateGEP(IdPtr, ConstantInt::get(Int64Ty, 1));

        // store incremented id_ptr
        IRB.CreateStore(NewIdPtr, AFLIdPtr)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
#else
        //   %27 = load i32, i32* @__afl_prev_loc, !dbg !30, !nosanitize !2
        //   %28 = load i8*, i8** @__afl_area_ptr, !dbg !30, !nosanitize !2
        //   %29 = xor i32 %27, 33851, !dbg !30
        //   %30 = getelementptr i8, i8* %28, i32 %29, !dbg !30
        //   %31 = load i8, i8* %30, !dbg !30, !nosanitize !2
        //   %32 = add i8 %31, 1, !dbg !30
        //   store i8 %32, i8* %30, !dbg !30, !nosanitize !2
        //   store i32 16925, i32* @__afl_prev_loc, !dbg !30, !nosanitize !2

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
#endif
      }

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN") ? "hardened" : "non-hardened",
             inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
