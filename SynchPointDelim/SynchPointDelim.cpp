//===- Identify Synchronization Points, DRF Paths and Data Conflicts ------===//
// Analysis Compiler Pass to Identify the synchronization points and the
// data conflicts over them
//===----------------------------------------------------------------------===//
// Created at 1/2 -16
// Jonatan Waern
//===----------------------------------------------------------------------===//

// #include <sstream>
#include <iostream>
#include <string>

// #include <stack>
// #include <set>
// #include <queue>
// #include <list>
// #include <map>
// #include <utility>
// #include <algorithm>
// #include <map>

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/InstIterator.h"

// #include "llvm/ADT/SmallVector.h"
// #include "llvm/ADT/ArrayRef.h"
// #include "llvm/ADT/APInt.h"

#include "llvm/IR/Instruction.h"
// #include "llvm/IR/Instructions.h"
// #include "llvm/IR/Constants.h"
// #include "llvm/IR/IRBuilder.h"
// #include "llvm/IR/Function.h"
// #include "llvm/IR/Module.h"
// #include "llvm/IR/BasicBlock.h"
// #include "llvm/IR/Value.h"
// #include "llvm/IR/Intrinsics.h"
// #include "llvm/IR/Metadata.h"
// #include "llvm/IR/CFG.h"
// #include "llvm/IR/DerivedTypes.h"
// #include "llvm/IR/Dominators.h"
// #include "llvm/IR/InstIterator.h"
// #include "llvm/IR/Constants.h"
// #include "llvm/IR/Attributes.h"
// #include "llvm/IR/NoFolder.h"

//#include "../Utils/SkelUtils/CallingDAE.cpp"
//#include "../Utils/SkelUtils/MetadataInfo.h"

// #include "llvm/Analysis/LoopInfo.h"
// #include "llvm/Analysis/CFG.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/TargetLibraryInfo.h"
// #include "llvm/Analysis/MemoryLocation.h"
// #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

// #include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"

#include "SynchPoint.hpp"

#define LIBRARYNAME "SynchPointDelim"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT_VERBOSE PRINTSTREAM << "SynchPointDelim: "
#define PRINT_DEBUG PRINTSTRREAM << "SynchPointDelim (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT_VERBOSE << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

namespace {
    //These are the functions to treat as synchronization points
    set<StringRef> SynchFunctions = {}

    struct SynchPointDelim : public ModulePass {
        static char ID;
        SynchPointDelim() : ModulePass(ID) {}

    public:
        int DR_ID;
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            //AU.addRequired<DominatorTreeWrapperPass>();
            //AU.addRequired<AliasAnalysis>();
            //AU.addRequired<ScalarEvolution>();
            //AU.addRequired<TargetLibraryInfoWrapperPass>();
            //AU.addRequired<LoopInfoWrapperPass>();
            //Here we would "require" the previous AA pass
        }

        //Assume input module is inlined as far as possible
        //

        //The main runOnModule function is divided in two parts
        //The first part finds synchronization points and the drf paths between
        //them
        //The second part determines which synchronization points synch with
        //eachother, and finds data conflicts across synchronizations points
        virtual bool runOnModule(Module &M) {
            
            return false; //Pure analysis, should not change any code
        }

        //These data structures are the results of the analysis
        //TODO: There should propably be interface functions towards
        //synchronization variables that mean that direct access
        //to synchronizationPoints are not necessary
        SmallPtrSet<SynchronizationPoint*,32> synchronizationPoints;
        SmallPtrSet<SynchronizationVariable*,8> synchronizationVariables;

    private:
        //Top-level delimitation for a function, should commonly only be
        //called on main
        //Disregards synchronization until the point that a thread has been
        //created
        void topLevelDelimitForFunction(Function *functionStart) {
            
        }

        //Starts proper delimitation at a particular instruction
        void delimitFromInstruction(Instruction *start) {
        }

        //Utility: Searches a SmallPtrSet for a SynchronizationPoint
        //with a particular instruction value
        SynchronizationPoint *findSynchPoint(SmallPtrSet<SynchronizationPoints*,32>
                                             synchSet, Instruction* inst) {
            for (SynchronizationPoint *examine : synchSet) {
                if (examine->val == inst)
                    return examine;
            }

            return NULL;
        }
    };
}

char SynchPointDelim::ID = 0;
static RegisterPass<SynchPointDelim> X("SPDelim",
                                       "Identify Synch Points and Data Conflicts pass",
                                       true,
                                       true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
