#ifndef _XDRFEXTENSION_
#define _XDRFEXTENSION_
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

// #include "llvm/ADT/SmallVector.h"
// #include "llvm/ADT/ArrayRef.h"
// #include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallPtrSet.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
//#include "llvm/IR/Constants.h"
// #include "llvm/IR/IRBuilder.h"
//#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
//#include "llvm/IR/BasicBlock.h"
//#include "llvm/IR/Value.h"
// #include "llvm/IR/Intrinsics.h"
// #include "llvm/IR/Metadata.h"
// #include "llvm/IR/CFG.h"
// #include "llvm/IR/DerivedTypes.h"
// #include "llvm/IR/Dominators.h"
//#include "llvm/IR/InstIterator.h"
//#include "llvm/IR/Constants.h"
// #include "llvm/IR/Attributes.h"
// #include "llvm/IR/NoFolder.h"

//#include "../Utils/SkelUtils/CallingDAE.cpp"
//#include "../Utils/SkelUtils/MetadataInfo.h"

// #include "llvm/Analysis/LoopInfo.h"
//#include "llvm/Analysis/CFG.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/TargetLibraryInfo.h"
// #include "llvm/Analysis/MemoryLocation.h"
// #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

// #include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"

//#include "../SynchPointDelim/SynchPointDelim.cpp"
#include "../SynchPointDelim/SynchPointDelim.cpp"
#include "../SynchPointDelim/SynchPoint.hpp"
#include "../SynchPointDelim/UseChainAliasing.cpp"

#define LIBRARYNAME "XDRFExtension"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "XDRFExtension: "
#define PRINT_DEBUG PRINTSTREAM << "XDRFExtension (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE("light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

struct nDRFRegion {
    nDRFRegion() {
        static int rID = 0;
        ID = rID++;
    }
    int ID;

    SmallPtrSet<Instruction*,2> beginsAt;
    SmallPtrSet<Instruction*,2> endsAt;
    SmallPtrSet<Instruction*,128> containedInstructions;
    SmallPtrSet<nDRFRegion*,2> precedingRegions;
    SmallPtrSet<nDRFRegion*,2> followingRegions;
    SmallPtrSet<Instruction*,128> precedingInstructions;
    SmallPtrSet<Instruction*,128> followingInstructions;
    SmallPtrSet<nDRFRegion*,2> synchsWith;
    set<pair<Instruction*,Instruction*> > conflicts;
    bool receivesSignal=false, sendsSignal=false;
    bool enclave=false;
};

namespace {

    struct XDRFExtension : public ModulePass {
        static char ID;
        XDRFExtension() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            //AU.addRequired<AliasAnalysis>();
            AU.addRequired<SynchPointDelim>();
            //Here we would "require" the previous AA pass
        }
      
        virtual bool runOnModule(Module &M) {
            SynchPointDelim &syncdelimited  = getAnalysis<SynchPointDelim>();
            setupNDRFRegions(syncdelimited);
            //calculate enclaveness
            printInfo();
            return false;
        }

        SmallPtrSet<nDRFRegion*,4> nDRFRegions;

        void setupNDRFRegions(SynchPointDelim &syncdelimited) {
            map<SynchronizationVariable*,SmallPtrSet<nDRFRegion*,2> > nDRFRegionsSynchsOn;
            map<SynchronizationPoint*,nDRFRegion*> regionOfPoint;
            //For now, plainly transfer the info into an nDRF region
            for (CriticalRegion * critRegion : syncdelimited.criticalRegions) {
                nDRFRegion* newRegion = new nDRFRegion;
                //Setup what nDRF regions synchronize with each other
                for (SynchronizationVariable* synch :  critRegion->synchsOn) {
                    for (nDRFRegion* synchsWith : nDRFRegionsSynchsOn[synch]) {
                        newRegion->synchsWith.insert(synchsWith);
                        synchsWith->synchsWith.insert(newRegion);
                    }
                    nDRFRegionsSynchsOn[synch].insert(newRegion);
                }
            
                //Setup entries and exits of new region
                //also setup preceding and following instructions and nDRF regions
                for (SynchronizationPoint* entry : critRegion->entrySynchPoints) {
                    newRegion->beginsAt.insert(entry->val);
                    newRegion->precedingInstructions=entry->getPrecedingInsts();
                    for (SynchronizationPoint* pred : entry->preceding) {
                        if (pred) {
                            if (regionOfPoint[pred]) {
                                newRegion->precedingRegions.insert(regionOfPoint[pred]);
                                regionOfPoint[pred]->followingRegions.insert(newRegion);
                            }
                        }
                    }
                }
                for (SynchronizationPoint* exit : critRegion->exitSynchPoints) {
                    newRegion->endsAt.insert(exit->val);
                    newRegion->followingInstructions=exit->getFollowingInsts();
                    for (SynchronizationPoint* follow : exit->following) {
                        if (follow) {
                            if (regionOfPoint[follow]) {
                                newRegion->followingRegions.insert(regionOfPoint[follow]);
                                regionOfPoint[follow]->precedingRegions.insert(newRegion);
                            }
                        }
                    }
                }
                
                //Setup the contained instructions
                for (SynchronizationPoint* in : critRegion->containedSynchPoints) {
                    regionOfPoint[in]=newRegion;
                    if (in->isOnewayFrom)
                        newRegion->sendsSignal=true;
                    if (in->isOnewayTo)
                        newRegion->receivesSignal=true;
                    
                    for (SynchronizationPoint* after : in->following) {
                        if (critRegion->containedSynchPoints.count(after) != 0) {
                            newRegion->containedInstructions.insert(in->followingInsts[after].begin(),
                                                                    in->followingInsts[after].end());
                        }
                    }
                }
                nDRFRegions.insert(newRegion);
            }
        }

        

        void printInfo() {
            VERBOSE_PRINT("Printing nDRF region info...\n");
            for (nDRFRegion * region : nDRFRegions) {
                VERBOSE_PRINT("Region " << region->ID << ":\n");
                if (region->receivesSignal)
                    VERBOSE_PRINT("  Receives signals\n");
                if (region->sendsSignal)
                    VERBOSE_PRINT("  Sends signals\n");
                VERBOSE_PRINT("  Begins at:\n");
                for (Instruction * inst : region->beginsAt) {
                    VERBOSE_PRINT("   " << *inst << "\n");
                }
                VERBOSE_PRINT("  Ends at:\n");
                for (Instruction * inst : region->endsAt) {
                    VERBOSE_PRINT("   " << *inst << "\n");
                }
                VERBOSE_PRINT("  Preceded by " << region->precedingInstructions.size() << " instructions\n");
                VERBOSE_PRINT("  Contains " << region->containedInstructions.size() << " instructions\n");
                VERBOSE_PRINT("  Followed by " << region->followingInstructions.size() << " instructions\n");
                VERBOSE_PRINT("  Preceded by the nDRF regions:\n");
                for (nDRFRegion * pred : region->precedingRegions) {
                        VERBOSE_PRINT("   " << pred->ID << "\n");
                }
                VERBOSE_PRINT("  Followed by the nDRF regions:\n");
                for (nDRFRegion * follow : region->followingRegions) {
                        VERBOSE_PRINT("   " << follow->ID << "\n");
                }
            }
        }

    };
}

char XDRFExtension::ID = 0;
static RegisterPass<XDRFExtension> Y("XDRFextend",
				     "Identifies nDRF and XDRF regions",
				     true,
				     true);
#endif

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
