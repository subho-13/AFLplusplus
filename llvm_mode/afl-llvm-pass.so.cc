/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski

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

#define AFL_LLVM_PASS

#include "config.h"
#include "debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <list>
#include <string>
#include <fstream>
#include <cstdlib>
#include <iostream>

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/raw_ostream.h" /* needed for llvm 3.8 */

struct bb_id {

  std::string * bb;
  uint32_t      id;
  struct bb_id *next;

};

using namespace llvm;

namespace {

class AFLCoverage : public ModulePass {

 public:
  static char ID;
  AFLCoverage() : ModulePass(ID) {

    char *instWhiteListFilename = getenv("AFL_LLVM_WHITELIST");

    if (instWhiteListFilename) {

      std::string   line;
      std::ifstream fileStream;
      fileStream.open(instWhiteListFilename);
      if (!fileStream) report_fatal_error("Unable to open AFL_LLVM_WHITELIST");
      getline(fileStream, line);
      while (fileStream) {

        myWhitelist.push_back(line);
        getline(fileStream, line);

      }

    }

    if (getenv("AFL_DEBUG")) debug = 1;

  }

  static std::string getSimpleNodeLabel(const BasicBlock *BB,
                                        const Function *) {

    if (!BB->getName().empty()) return BB->getName().str();

    std::string        Str;
    raw_string_ostream OS(Str);

    BB->printAsOperand(OS, false);
    return OS.str();

  }

  bool runOnModule(Module &M) override;

  // StringRef getPassName() const override {

  //  return "American Fuzzy Lop Instrumentation";
  // }

 protected:
  std::list<std::string> myWhitelist;
  int                    debug = 0;

};

}  // namespace

char AFLCoverage::ID = 0;

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  unsigned int cur_loc = 0;

  /* Show a banner */

  char be_quiet = 0;

  if (debug) fprintf(stderr, "DEBUG: NEW FILE\n");

  if (getenv("AFL_DEBUG") || (isatty(2) && !getenv("AFL_QUIET"))) {

    SAYF(cCYA "afl-llvm-pass" VERSION cRST " by <lszekeres@google.com>\n");

  } else if (getenv("AFL_QUIET"))

    be_quiet = 1;

  /* Decide instrumentation ratio */

  char *       inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  char          *fn = NULL, *lockfile = NULL;
  int            collisions = 0, unknown = 0, fd;
  unsigned char *ids = NULL, *map = NULL;
  bb_id         *bb_list = NULL, *bb_cur;

  if ((fn = getenv("AFL_LLVM_CHECK_COLLISIONS")) != NULL) {
    int first = 1, len;
    if ((lockfile = (char *)malloc(strlen(fn) + 5)) == NULL) PFATAL("memory");
    snprintf(lockfile, strlen(fn) + 5, "%s.lck", fn);
    while ((fd = open(lockfile, O_CREAT | O_EXCL | O_RDWR, 0600)) < 0) {

      if (first) {

        SAYF(cYEL "[!] " cBRI
                  "Lock file is present, waiting for other tasks to finish. -j "
                  "can not be used in AFL_LLVM_NON_COLLIDING_COVERAGE mode."
                  " If this is an error, please delete %s and %s\n", fn, lockfile);
        first = 0;

      }

      sleep(1);

    }

    close(fd);

    if ((map = (unsigned char *)malloc(MAP_SIZE)) == NULL) PFATAL("memory");
    if ((ids = (unsigned char *)malloc(MAP_SIZE)) == NULL) PFATAL("memory");

    if ((fd = open(fn, O_CREAT | O_EXCL | O_RDWR, 0600)) < 0) {
 
      // the file exists already, so we have to read its contents
      if ((fd = open(fn, O_CREAT | O_RDWR, 0600)) < 0)
        PFATAL("cannot open instrumentation counter file");
      if ((len = read(fd, map, MAP_SIZE) < MAP_SIZE))
        PFATAL("cannot read instrumentation map file");
 
    }

    // we keep fd open

  }

#if LLVM_VERSION_MAJOR < 9
  char *neverZero_counters_str = getenv("AFL_LLVM_NOT_ZERO");
#endif

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

#ifdef __ANDROID__
  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc");
#else
  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc", 0,
      GlobalVariable::GeneralDynamicTLSModel, 0, false);
#endif

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<>          IRB(&(*IP));

      if (!myWhitelist.empty()) {

        bool instrumentBlock = false;

        /* Get the current location using debug information.
         * For now, just instrument the block if we are not able
         * to determine our location. */
        DebugLoc Loc = IP->getDebugLoc();
        if (Loc) {

          DILocation *cDILoc = dyn_cast<DILocation>(Loc.getAsMDNode());

          unsigned int instLine = cDILoc->getLine();
          StringRef    instFilename = cDILoc->getFilename();

          if (instFilename.str().empty()) {

            /* If the original location is empty, try using the inlined location
             */
            DILocation *oDILoc = cDILoc->getInlinedAt();
            if (oDILoc) {

              instFilename = oDILoc->getFilename();
              instLine = oDILoc->getLine();

            }

          }

          /* Continue only if we know where we actually are */
          if (!instFilename.str().empty()) {

            for (std::list<std::string>::iterator it = myWhitelist.begin();
                 it != myWhitelist.end(); ++it) {

              /* We don't check for filename equality here because
               * filenames might actually be full paths. Instead we
               * check that the actual filename ends in the filename
               * specified in the list. */
              if (instFilename.str().length() >= it->length()) {

                if (instFilename.str().compare(
                        instFilename.str().length() - it->length(),
                        it->length(), *it) == 0) {

                  instrumentBlock = true;
                  break;

                }

              }

            }

          }

        }

        /* Either we couldn't figure out our location or the location is
         * not whitelisted, so we skip instrumentation. */
        if (!instrumentBlock) continue;

      }

      if (AFL_R(100) >= inst_ratio) continue;

/* There is a problem with Ubuntu 18.04 and llvm 6.0 (see issue #63).
   The inline function successors() is not inlined and also not found at runtime
   :-( As I am unable to detect Ubuntu18.04 heree, the next best thing is to
   disable this optional optimization for LLVM 6.0.0 and Linux */
#if !(LLVM_VERSION_MAJOR == 6 && LLVM_VERSION_MINOR == 0) || !defined __linux__

        // only instrument if this basic block is the destination of a previous
        // basic block that has multiple successors
        // this gets rid of ~5-10% of instrumentations that are unnecessary
        // result: a little more speed and less map pollution
        int more_than_one = -1;
        // fprintf(stderr, "BB %u: ", cur_loc);
        for (BasicBlock *Pred : predecessors(&BB)) {

          int count = 0;
          if (more_than_one == -1) more_than_one = 0;
          // fprintf(stderr, " %p=>", Pred);

          for (BasicBlock *Succ : successors(Pred)) {

            // if (count > 0)
            //  fprintf(stderr, "|");
            if (Succ != NULL) count++;
            // fprintf(stderr, "%p", Succ);

          }

          if (count > 1) more_than_one = 1;

        }

        // fprintf(stderr, " == %d\n", more_than_one);
        if (more_than_one != 1) continue;

#endif

      /* Make up cur_loc */


      cur_loc = AFL_R(MAP_SIZE);

      if (fn) {  // AFL_LLVM_CHECK_COLLISIONS

        std::string bb_name = getSimpleNodeLabel(&BB, &F);

        if (bb_list == NULL) {  // very first basic block

          if ((bb_list = (struct bb_id *)malloc(sizeof(struct bb_id))) == NULL)
            PFATAL("malloc");
          bb_list->bb =
              new std::string(bb_name);  // strdup(LLVMGetBasicBlockName(&BB));
          bb_list->id = cur_loc;
          bb_list->next = NULL;

        } else {

          for (BasicBlock *Pred : predecessors(&BB)) {

            assert(Pred != NULL);
            bb_cur = bb_list;
            std::string pred_name = getSimpleNodeLabel(Pred, &F);

            while (bb_cur != NULL && pred_name.compare(*bb_cur->bb) != 0)
              bb_cur = bb_cur->next;

            if (bb_cur != NULL) {  // predecessor has a cur_loc

              if (map[(bb_cur->id >> 1) ^ cur_loc] > 0)
                collisions++;
              map[(bb_cur->id >> 1) ^ cur_loc]++;
                
            } else { // this pred does not have a cur_loc yet ... damn

              unknown++;

            }

          }

        }                                         /* end of bb_list != NULL */

      }

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

#if LLVM_VERSION_MAJOR < 9
      if (neverZero_counters_str !=
          NULL) {  // with llvm 9 we make this the default as the bug in llvm is
                   // then fixed
#endif
        /* hexcoder: Realize a counter that skips zero during overflow.
         * Once this counter reaches its maximum value, it next increments to 1
         *
         * Instead of
         * Counter + 1 -> Counter
         * we inject now this
         * Counter + 1 -> {Counter, OverflowFlag}
         * Counter + OverflowFlag -> Counter
         */
        /*       // we keep the old solutions just in case
                 // Solution #1
                 if (neverZero_counters_str[0] == '1') {

                   CallInst *AddOv =
           IRB.CreateBinaryIntrinsic(Intrinsic::uadd_with_overflow, Counter,
           ConstantInt::get(Int8Ty, 1));
                   AddOv->setMetadata(M.getMDKindID("nosanitize"),
           MDNode::get(C, None)); Value *SumWithOverflowBit = AddOv; Incr =
           IRB.CreateAdd(IRB.CreateExtractValue(SumWithOverflowBit, 0),  // sum
                                        IRB.CreateZExt( // convert from one bit
           type to 8 bits type IRB.CreateExtractValue(SumWithOverflowBit, 1), //
           overflow Int8Ty));
                  // Solution #2

                  } else if (neverZero_counters_str[0] == '2') {

                     auto cf = IRB.CreateICmpEQ(Counter,
           ConstantInt::get(Int8Ty, 255)); Value *HowMuch =
           IRB.CreateAdd(ConstantInt::get(Int8Ty, 1), cf); Incr =
           IRB.CreateAdd(Counter, HowMuch);
                  // Solution #3

                  } else if (neverZero_counters_str[0] == '3') {

        */
        // this is the solution we choose because llvm9 should do the right
        // thing here
        auto cf = IRB.CreateICmpEQ(Incr, ConstantInt::get(Int8Ty, 0));
        auto carry = IRB.CreateZExt(cf, Int8Ty);
        Incr = IRB.CreateAdd(Incr, carry);
/*
         // Solution #4

         } else if (neverZero_counters_str[0] == '4') {

            auto cf = IRB.CreateICmpULT(Incr, ConstantInt::get(Int8Ty, 1));
            auto carry = IRB.CreateZExt(cf, Int8Ty);
            Incr = IRB.CreateAdd(Incr, carry);

         } else {

            fprintf(stderr, "Error: unknown value for AFL_NZERO_COUNTS: %s
   (valid is 1-4)\n", neverZero_counters_str); exit(-1);

         }

*/
#if LLVM_VERSION_MAJOR < 9

      }

#endif

      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* cleanup */

  if (fn) {                              /* AFL_LLVM_NON_COLLIDING_COVERAGE */
    // write map
    if (debug) fprintf(stderr, "DEBUG: done with source file, finishing ...\n");
    lseek(fd, 0, SEEK_SET);
    if (write(fd, map, MAP_SIZE) < MAP_SIZE)
      PFATAL("write to instrumentation counter file failed");
    close(fd);
    unlink(lockfile);
    free(lockfile);
    free(map);
    map = NULL;
  }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else if (fn) {

      OKF("Instrumented %u locations with %d collision(s) and %d unknown (%s mode, ratio "
          "%u%%).",
          inst_blocks, collisions, unknown,
          getenv("AFL_HARDEN")
              ? "hardened"
              : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
                     ? "ASAN/MSAN"
                     : "non-hardened"),
          inst_ratio);

    } else {

      OKF("Instrumented %u locations (%s mode, ratio %u%%).", inst_blocks,
          getenv("AFL_HARDEN")
              ? "hardened"
              : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
                     ? "ASAN/MSAN"
                     : "non-hardened"),
          inst_ratio);

    }

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

