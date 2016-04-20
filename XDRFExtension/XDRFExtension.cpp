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
#include "../PointerAliasing/AliasCombiner.cpp"

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

static cl::opt<string> graphOutput2("g2", cl::desc("Specify output dot file for nDRF region graph"),
                                    cl::value_desc("filename"));

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
    map<nDRFRegion*,SmallPtrSet<Instruction*,16> > precedingInstructions;
    map<nDRFRegion*,SmallPtrSet<Instruction*,16> > followingInstructions;
    SmallPtrSet<nDRFRegion*,2> synchsWith;
    set<pair<Instruction*,Instruction*> > conflictsBetweenDRF;
    set<pair<Instruction*,pair<nDRFRegion*,Instruction*> > > conflictsTowardsDRF;
    bool receivesSignal=false, sendsSignal=false;
    bool enclave=false;
    bool startHere=false;

    SmallPtrSet<Instruction*,128> getPrecedingInsts() {
        SmallPtrSet<Instruction*,128> toReturn;
        for (nDRFRegion* region : precedingRegions)
            toReturn.insert(precedingInstructions[region].begin(),
                            precedingInstructions[region].end());
        return toReturn;
    }
    
    SmallPtrSet<Instruction*,128> getFollowingInsts() {
        SmallPtrSet<Instruction*,128> toReturn;
        for (nDRFRegion* region : followingRegions)
            toReturn.insert(followingInstructions[region].begin(),
                            followingInstructions[region].end());
        return toReturn;
    }
};

namespace {

    struct XDRFExtension : public ModulePass {
        static char ID;
        XDRFExtension() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            AU.addRequired<AliasAnalysis>();
            AU.addRequired<SynchPointDelim>();
            //Here we would "require" the previous AA pass
        }
      
        AliasCombiner *aacombined;

        virtual bool runOnModule(Module &M) {
            SynchPointDelim &syncdelimited  = getAnalysis<SynchPointDelim>();
            VERBOSE_PRINT("Setting up nDRF regions\n");
            setupNDRFRegions(syncdelimited);
            printInfo();
            printnDRFRegionGraph(M);
            AliasAnalysis &aa = getAnalysis<AliasAnalysis>();
            aacombined = new AliasCombiner(&M,true,MustAlias);
            aacombined->addAliasResult(aa);
            VERBOSE_PRINT("Extending DRF regions across nDRF regions\n");
            for (nDRFRegion * region : nDRFRegions)
                if (region->startHere) {
                    VERBOSE_PRINT("Starting from region: " << region->ID << "\n");
                    extendDRFRegion(region);
                }
            return false;
        }

        SmallPtrSet<nDRFRegion*,4> nDRFRegions;

        void setupNDRFRegions(SynchPointDelim &syncdelimited) {
            map<SynchronizationVariable*,SmallPtrSet<nDRFRegion*,2> > nDRFRegionsSynchsOn;
            map<SynchronizationPoint*,nDRFRegion*> regionOfPoint;
            //For now, plainly transfer the info into an nDRF region
            for (CriticalRegion * critRegion : syncdelimited.criticalRegions) {
                nDRFRegion* newRegion = new nDRFRegion;
                
                if (critRegion->firstRegionInEntry)
                    newRegion->startHere=true;
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
                    //newRegion->precedingInstructions=entry->getPrecedingInsts();
                    for (SynchronizationPoint* pred : entry->preceding) {
                        if (pred) {
                            nDRFRegion *regofpoint=regionOfPoint[pred];
                            if (regofpoint) {
                                newRegion->precedingInstructions[regofpoint].insert(entry->precedingInsts[pred].begin(),
                                                                                    entry->precedingInsts[pred].end());
                                newRegion->precedingRegions.insert(regofpoint);
                                regofpoint->followingRegions.insert(newRegion);
                            }
                        } else {
                            newRegion->precedingInstructions[NULL].insert(entry->precedingInsts[NULL].begin(),
                                                                          entry->precedingInsts[NULL].end());
                            newRegion->precedingRegions.insert(NULL);
                        }
                    }
                }
                for (SynchronizationPoint* exit : critRegion->exitSynchPoints) {
                    newRegion->endsAt.insert(exit->val);
                    //newRegion->followingInstructions=exit->getFollowingInsts();
                    for (SynchronizationPoint* follow : exit->following) {
                        if (follow) {
                            nDRFRegion *regofpoint=regionOfPoint[follow];
                            if (regofpoint) {
                                newRegion->followingInstructions[regofpoint].insert(exit->followingInsts[follow].begin(),
                                                                                    exit->followingInsts[follow].end());
                                newRegion->followingRegions.insert(regofpoint);
                                regofpoint->precedingRegions.insert(newRegion);
                            }
                        } else {
                            newRegion->followingInstructions[NULL].insert(exit->followingInsts[NULL].begin(),
                                                                          exit->followingInsts[NULL].end());
                            newRegion->followingRegions.insert(NULL);
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
                        if (critRegion->containedSynchPoints.count(after) != 0 &&
                            //The preceding point being an exit point implies that we should not count instructions between it and
                            //following regions that are not exit points in this region
                            (!(critRegion->exitSynchPoints.count(in) != 0) || critRegion->exitSynchPoints.count(after) != 0))
                            {
                            newRegion->containedInstructions.insert(in->followingInsts[after].begin(),
                                                                    in->followingInsts[after].end());
                        }
                    }
                }
                nDRFRegions.insert(newRegion);
            }
        }

        void printnDRFRegionGraph(Module &M) {
            ofstream outputGraph(graphOutput2.c_str());
            if (outputGraph.is_open()) {
                outputGraph << "digraph \"" << (M.getName().data()) << " nDRF Region Graph\" {\n";
                for (nDRFRegion * region : nDRFRegions) {
                    for (nDRFRegion * regionTo : region->followingRegions) {
                        if (regionTo)
                            outputGraph << region->ID << " -> " << regionTo->ID << ";\n";
                        else
                            outputGraph << "\"Thread End\" -> " << regionTo->ID << ";\n";
                    }
                    if (region->startHere)
                        outputGraph << "\"Thread Start\" -> " << region->ID << ";\n";
                }
                outputGraph << "}\n";
                outputGraph.close();
            } else if (graphOutput.compare("") == 0) {
                VERBOSE_PRINT("Failed to output nDRF region graph\n");
            }
        }


        //Returns a pair:
        //first = instructions to check towards
        //Second = regions that follow us
        map<nDRFRegion*,pair<SmallPtrSet<Instruction*,64>, SmallPtrSet<nDRFRegion*,2> > > extendDRFRegionDynamic;
        pair<SmallPtrSet<Instruction*,64>,SmallPtrSet<nDRFRegion*,2> > extendDRFRegion(nDRFRegion *regionToExtend) {
            if (extendDRFRegionDynamic.count(regionToExtend) != 0)
                return extendDRFRegionDynamic[regionToExtend];

            //Obtain what to compare against
            SmallPtrSet<Instruction*,64> toCompareAgainst;
            SmallPtrSet<nDRFRegion*,2> followingRegions;

            //Handle end of context
            if (regionToExtend == NULL)
                return make_pair(toCompareAgainst,followingRegions);

            VERBOSE_PRINT("Handling region " << regionToExtend->ID << "\n");

            //Handle special cases, signals and waits are never xDRF
            if (regionToExtend->receivesSignal || regionToExtend->sendsSignal) {
                regionToExtend->enclave=false;
                return make_pair(toCompareAgainst,followingRegions);
            }

            //Handles recursive cases
            extendDRFRegionDynamic[regionToExtend]=make_pair(toCompareAgainst,followingRegions);


            //Obtain the instructions to compare from regions that follow us
            for (nDRFRegion * region : regionToExtend->followingRegions) {
                toCompareAgainst.insert(regionToExtend->followingInstructions[regionToExtend].begin(),
                                        regionToExtend->followingInstructions[regionToExtend].end());
                followingRegions.insert(region);
                pair<SmallPtrSet<Instruction*,64>, SmallPtrSet<nDRFRegion*,2> > recursiveCompareAgainst = extendDRFRegion(region);
                toCompareAgainst.insert(recursiveCompareAgainst.first.begin(),
                                        recursiveCompareAgainst.first.end());
                followingRegions.insert(recursiveCompareAgainst.second.begin(),
                                        recursiveCompareAgainst.second.end());
            }

            //Obtain the instructions to compare from regions that synch with us
            for (nDRFRegion * region : regionToExtend->synchsWith) {
                pair<SmallPtrSet<Instruction*,64>, SmallPtrSet<nDRFRegion*,2> > recursiveCompareAgainst = extendDRFRegion(region);
                followingRegions.insert(region);
                toCompareAgainst.insert(recursiveCompareAgainst.first.begin(),
                                        recursiveCompareAgainst.first.end());
                followingRegions.insert(recursiveCompareAgainst.second.begin(),
                                        recursiveCompareAgainst.second.end());
            }

            // VERBOSE_PRINT("Handling " << regionToExtend->ID << " need to make " << (regionToExtend->getPrecedingInsts().size() * toCompareAgainst.size()) << " + " << (regionToExtend->containedInstructions.size() * (regionToExtend->getPrecedingInsts().size() + toCompareAgainst.size())) << " comparisons (or more)\n");
            
            VERBOSE_PRINT("Handling " << regionToExtend->ID << ":\n");
            VERBOSE_PRINT("  Has " << regionToExtend->getPrecedingInsts().size() << " preceding instructions\n"); 
            VERBOSE_PRINT("  Contains " << regionToExtend->containedInstructions.size() << " instructions\n");
            VERBOSE_PRINT("  Must compare against " << toCompareAgainst.size() << " following instructions\n");
            VERBOSE_PRINT("  And " << followingRegions.size() << " regions\n");
            bool conflict = false;
            //Cross-check
            for (Instruction * instPre : regionToExtend->getPrecedingInsts()) {    
                for (Instruction * instAfter : toCompareAgainst) {
                    //Comparing instructions to themselves, in case of loops, is perfectly fine
                    if (aacombined->MayConflict(instPre,instAfter)) {
                        regionToExtend->conflictsBetweenDRF.insert(make_pair(instPre,instAfter));
                        conflict=true;
                    }
                }
                //Check our preceding instructions towards the instructions inside the following nDRFs
                for (nDRFRegion * region : followingRegions) {
                    if (region) {
                        for (Instruction * instIn : region->containedInstructions) {
                            if (aacombined->MayConflict(instPre,instIn)) {
                                region->conflictsTowardsDRF.insert(make_pair(instPre,make_pair(region,instIn)));
                                conflict=true;
                            }
                        }
                    }
                }
            }
            //Check the instructions within our nDRF towards all previous and following insts
            for (Instruction * instIn : regionToExtend->containedInstructions) {
                for (Instruction * instPre : regionToExtend->getPrecedingInsts()) {   
                    if (aacombined->MayConflict(instPre,instIn)) {
                        regionToExtend->conflictsTowardsDRF.insert(make_pair(instPre,make_pair(regionToExtend,instIn)));
                        conflict=true;
                    }
                }
                for (Instruction * instAfter : toCompareAgainst) {   
                    if (aacombined->MayConflict(instAfter,instIn)) {
                        regionToExtend->conflictsTowardsDRF.insert(make_pair(instAfter,make_pair(regionToExtend,instIn)));
                        conflict=true;
                    }
                }
            }

            //If no conflicts are detected by extending over us, make us enclave
            if (!conflict) {
                regionToExtend->enclave=true;
            } else {
                regionToExtend->enclave=false;
                //Otherwise, the things that follow us are not of interest to our parent
                toCompareAgainst.clear();
                followingRegions.clear();
            }

            return extendDRFRegionDynamic[regionToExtend]=make_pair(toCompareAgainst,followingRegions);
        }
        
        void printInfo() {
            VERBOSE_PRINT("Printing nDRF region info...\n");
            for (nDRFRegion * region : nDRFRegions) {
                VERBOSE_PRINT("Region " << region->ID << ":\n");
                if (region->enclave)
                    VERBOSE_PRINT("Is enclave\n");
                else
                    VERBOSE_PRINT("Is not enclave\n");
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
                SmallPtrSet<Instruction*,128> precedingInsts = region->getPrecedingInsts();
                SmallPtrSet<Instruction*,128> followingInsts = region->getFollowingInsts();
                VERBOSE_PRINT("  Preceded by " << precedingInsts.size() << " instructions\n");
                VERBOSE_PRINT("  Contains " << region->containedInstructions.size() << " instructions\n");
                VERBOSE_PRINT("  Followed by " << followingInsts.size() << " instructions\n");
                VERBOSE_PRINT("  Preceded by the nDRF regions:\n");
                for (nDRFRegion * pred : region->precedingRegions) {
                    if (pred)
                        VERBOSE_PRINT("   " << pred->ID << "\n");
                    else
                        VERBOSE_PRINT("   Thread Entry\n");
                }
                VERBOSE_PRINT("  Followed by the nDRF regions:\n");
                for (nDRFRegion * follow : region->followingRegions) {
                    if (follow)
                        VERBOSE_PRINT("   " << follow->ID << "\n");
                    else
                        VERBOSE_PRINT("   Thread Entry\n");
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
