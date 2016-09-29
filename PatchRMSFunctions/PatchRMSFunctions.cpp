//===-------------------- Patchs RMS Functions  ---------------------===//
// Adds the readonly attributes ot parameters of RMS functions
//===----------------------------------------------------------------------===//
// Created at 29/9 -16
// Jonatan Waern
//===----------------------------------------------------------------------===//

// #include <sstream>
#include <iostream>
#include <string>

// #include <stack>
#include <set>
#include <vector>
#include <deque>
// #include <list>
// #include <map>
#include <utility>
// #include <algorithm>

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/InstIterator.h"
#include "llvm/Support/Debug.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/ArrayRef.h"
// #include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallPtrSet.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
// #include "llvm/IR/Intrinsics.h"
// #include "llvm/IR/Metadata.h"
// #include "llvm/IR/CFG.h"
// #include "llvm/IR/DerivedTypes.h"
// #include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
// #include "llvm/IR/Attributes.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InlineAsm.h"

// #include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/TargetLibraryInfo.h"
// #include "llvm/Analysis/MemoryLocation.h"
// #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"

#define LIBRARYNAME "PatchRMSFunctions"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "PatchRMSFunctions: "
#define PRINT_DEBUG PRINTSTREAM << "PatchRMSFunctions (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE("light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

#define MONXDRF 0
#define MOXDRF 1

#define TRACE_NUMBER 0

namespace {

    struct PatchRMSFunctions : public ModulePass {
        static char ID;
        PatchRMSFunctions() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
        }
      
        virtual bool runOnModule(Module &M) {

            VERBOSE_PRINT("Patching RMS functions in " << M.getName() << "\n");

            for (Function &fun : M.getFunctionList()) {
                if (fun.getName().startswith("RMS_")) {
                    VERBOSE_PRINT("Patching " << fun.getName() << "\n");
                    patchFunction(fun.getName(),M);
                }
            }
            
            return true;
        }
    private:

        //Patches the function in the specified module      
        void patchFunction(string name, Module &M) {
            Function * toModify=M.getFunction(name);
            if (!toModify) {
                VERBOSE_PRINT("Failed to modify " << name << ", was not found in module");
                return;
            }

            toModify->setOnlyReadsMemory();
            
        }
    };
}

char PatchRMSFunctions::ID = 0;
static RegisterPass<PatchRMSFunctions> Z("patch-rms",
                                         "Patches RMS functions with readonly attributes for parameters",
                                         true,
                                         true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
