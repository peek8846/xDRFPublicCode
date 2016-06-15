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

#include "llvm/Analysis/Passes.h"
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

//Shorthand for checking whether two accesses conflict
#define MAYCONFLICT(X,Y) ((isa<StoreInst>(X) || isa<StoreInst>(Y)) && aacombined->MayConflict(X,Y))

using namespace llvm;
using namespace std;

static cl::opt<string> graphOutput2("g2", cl::desc("Specify output dot file for nDRF region graph"),
                                    cl::value_desc("filename"));

static cl::opt<bool> skipConflictStore("nostore",cl::desc("Do not store data access conflict info"));

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

struct xDRFRegion {
    xDRFRegion() {
        static int rID = 0;
        ID = rID++;
    }
    int ID;

    SmallPtrSet<Instruction*,128> containedInstructions;
    SmallPtrSet<nDRFRegion*,2> enclaveNDRFs;
    SmallPtrSet<nDRFRegion*,2> precedingNDRFs;
    SmallPtrSet<nDRFRegion*,2> followingNDRFs;
    //Conflict between this xDRF region and another that prevents them from being merged
    //Also has the nDRF region separating them
    set<tuple<Instruction*,nDRFRegion*,Instruction*> > conflictsTowardsXDRF;
    set<pair<pair<nDRFRegion*,Instruction*>,pair<nDRFRegion*,Instruction*> > > conflictsTowardsNDRF;
    bool startHere=false;

    //Returns true if all the instructions in insts are in containedinstructions
    bool containsInstructions(SmallPtrSet<Instruction*,2> insts) {
        for (Instruction * inst : insts) {
            if (containedInstructions.count(inst) == 0)
                return false;
        }
        return true;
    }

    //Convenience call
    bool containsInstructions(Instruction * inst) {
        SmallPtrSet<Instruction*,2> insts;
        insts.insert(inst);
        return containsInstructions(insts);
    }

    //Convenience call
    bool containsInstructions(Instruction * inst1, Instruction * inst2) {
        SmallPtrSet<Instruction*,2> insts;
        insts.insert(inst1);
        insts.insert(inst2);
        return containsInstructions(insts);
    }
};


namespace {

    struct XDRFExtension : public ModulePass {
        static char ID;
        XDRFExtension() : ModulePass(ID) {
            //initializeXDRFExtensionPass(*PassRegistry::getPassRegistry())
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            AU.addRequired<AAResultsWrapperPass>();
            AU.addRequired<AssumptionCacheTracker>();
            AU.addRequired<TargetLibraryInfoWrapperPass>();
            AU.addRequired<SynchPointDelim>();
            AU.setPreservesAll();
        }
      
        AliasCombiner *aacombined;

        virtual bool runOnModule(Module &M) {
            SynchPointDelim &syncdelimited  = getAnalysis<SynchPointDelim>();
            VERBOSE_PRINT("Setting up nDRF regions\n");
            setupNDRFRegions(syncdelimited);
            printnDRFRegionGraph(M);
            //Pass &aa = getAnalysis<AAResultsWrapperPass>();
            aacombined = new AliasCombiner(&M,true,this,MustAlias);
            //aacombined->addAliasResult(&aa);
            VERBOSE_PRINT("Determining enclaveness of nDRF regions\n");
            for (nDRFRegion * region : nDRFRegions)
                if (region->startHere) {
                    VERBOSE_PRINT("Starting from region: " << region->ID << "\n");
                    extendDRFRegion(region);
                }
            VERBOSE_PRINT("Forming xDRF regions\n");
            for (nDRFRegion * region : nDRFRegions)
                if (region->startHere) {
                    VERBOSE_PRINT("Starting from region: " << region->ID << "\n");
                    xDRFRegion * startRegion = new xDRFRegion;
                    xDRFRegions.insert(startRegion);
                    consolidateXDRFRegions(region,startRegion);
                }
            printInfo();
            return false;
        }

        SmallPtrSet<nDRFRegion*,4> nDRFRegions;
        SmallPtrSet<xDRFRegion*,6> xDRFRegions;

        void setupNDRFRegions(SynchPointDelim &syncdelimited) {
            map<SynchronizationVariable*,SmallPtrSet<nDRFRegion*,2> > nDRFRegionsSynchsOn;
            map<SynchronizationPoint*,nDRFRegion*> regionOfPoint;
            //For now, plainly transfer the info into an nDRF region
            LIGHT_PRINT("Setting up nDRF regions\n");
            for (CriticalRegion * critRegion : syncdelimited.criticalRegions) {
                LIGHT_PRINT("Handling critical region " << critRegion->ID << "\n");
                nDRFRegion* newRegion = new nDRFRegion;
                LIGHT_PRINT("Created region " << newRegion->ID << "\n");
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
                    LIGHT_PRINT("Handling entrypoint " << entry->ID << "\n");
                    newRegion->beginsAt.insert(entry->val);
                    for (SynchronizationPoint* pred : entry->preceding) {
                        if (pred)
                            LIGHT_PRINT("Preceded by " << pred->ID << "\n");
                        else
                            LIGHT_PRINT("Preceded by context begin\n");                        
                        if (pred) {
                            nDRFRegion *regofpoint=regionOfPoint[pred];
                            if (regofpoint) {
                                LIGHT_PRINT("Which already had a region, setting up pred/follow towards " << regofpoint->ID << "\n");
                                newRegion->precedingInstructions[regofpoint].insert(entry->precedingInsts[pred].begin(),
                                                                                    entry->precedingInsts[pred].end());
                                LIGHT_PRINT("Added " << newRegion->precedingInstructions[regofpoint].size() << " preceding instructions\n");
                                
                                regofpoint->followingInstructions[newRegion].insert(entry->precedingInsts[pred].begin(),
                                                                                    entry->precedingInsts[pred].end());
                                LIGHT_PRINT("Added " << regofpoint->followingInstructions[newRegion].size() << " following instructions\n");
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
                    LIGHT_PRINT("Handling exitpoint " << exit->ID << "\n");
                    newRegion->endsAt.insert(exit->val);
                    for (SynchronizationPoint* follow : exit->following) {
                        if (follow)
                            LIGHT_PRINT("Followed by " << follow->ID << "\n");
                        else
                            LIGHT_PRINT("Followed by context end\n");                        
                        if (follow) {
                            nDRFRegion *regofpoint=regionOfPoint[follow];
                            if (regofpoint) {
                                LIGHT_PRINT("Which already had a region, setting up pred/follow towards " << regofpoint->ID << "\n");
                                newRegion->followingInstructions[regofpoint].insert(exit->followingInsts[follow].begin(),
                                                                                    exit->followingInsts[follow].end());
                                LIGHT_PRINT("Added " << newRegion->followingInstructions[regofpoint].size() << " following instructions\n");
                                regofpoint->precedingInstructions[newRegion].insert(exit->followingInsts[follow].begin(),
                                                                                    exit->followingInsts[follow].end());
                                LIGHT_PRINT("Added " << regofpoint->precedingInstructions[newRegion].size() << " preceding instructions\n");
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

            //Handles recursive cases
            extendDRFRegionDynamic[regionToExtend]=make_pair(toCompareAgainst,followingRegions);

            //Obtain the instructions to compare from regions that follow us
            for (nDRFRegion * region : regionToExtend->followingRegions) {
                toCompareAgainst.insert(regionToExtend->followingInstructions[region].begin(),
                                        regionToExtend->followingInstructions[region].end());
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

            //Handle special cases, signals and waits are never xDRF
            if (regionToExtend->receivesSignal || regionToExtend->sendsSignal) {
                regionToExtend->enclave=false;
                return extendDRFRegionDynamic[regionToExtend]=make_pair(toCompareAgainst,followingRegions);
            }
            
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
                    if (MAYCONFLICT(instPre,instAfter)) {
                        if (!skipConflictStore)
                            regionToExtend->conflictsBetweenDRF.insert(make_pair(instPre,instAfter));
                        DEBUG_PRINT("Found conflict between preceding and following DRF regions\n");
                        conflict=true;
                    }
                }
                //Check our preceding instructions towards the instructions inside the following nDRFs
                for (nDRFRegion * region : followingRegions) {
                    if (region) {
                        for (Instruction * instIn : region->containedInstructions) {
                            if (MAYCONFLICT(instPre,instIn)) {
                                if (!skipConflictStore)
                                    region->conflictsTowardsDRF.insert(make_pair(instPre,make_pair(region,instIn)));
                                DEBUG_PRINT("Found conflict between preceding DRF and following nDRF regions\n");
                                conflict=true;
                            }
                        }
                    }
                }
            }
            //Check the instructions within our nDRF towards all previous and following insts
            for (Instruction * instIn : regionToExtend->containedInstructions) {
                for (Instruction * instPre : regionToExtend->getPrecedingInsts()) {   
                    if (MAYCONFLICT(instPre,instIn)) {
                        if (!skipConflictStore)
                            regionToExtend->conflictsTowardsDRF.insert(make_pair(instPre,make_pair(regionToExtend,instIn)));
                        DEBUG_PRINT("Found conflict between nDRF region and preceding DRF regions\n");
                        conflict=true;
                    }
                }
                for (Instruction * instAfter : toCompareAgainst) {   
                    if (MAYCONFLICT(instAfter,instIn)) {
                        if (!skipConflictStore)
                            regionToExtend->conflictsTowardsDRF.insert(make_pair(instAfter,make_pair(regionToExtend,instIn)));
                        DEBUG_PRINT("Found conflict between nDRF region and following DRF regions\n");
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
                VERBOSE_PRINT("  Conflicts across region:\n");
                for (pair<Instruction*,Instruction*> conflict : region->conflictsBetweenDRF) {
                    VERBOSE_PRINT("    " << *(conflict.first) << " conflicts with " << *(conflict.second) << "\n");
                }
                VERBOSE_PRINT("  Conflicts towards DRF regions:\n");
                for (pair<Instruction*, pair<nDRFRegion*,Instruction*> > conflict : region->conflictsTowardsDRF) {
                    VERBOSE_PRINT("    DRF instruction" << *(conflict.first) << " conflicts with instruction" << *(conflict.second.second) << " in region with ID " << (conflict.second.first)->ID << "\n");
                }

            }
            VERBOSE_PRINT("Printing xDRF region info...\n");
            for (xDRFRegion * region : xDRFRegions) {
                VERBOSE_PRINT("Region " << region->ID << ":\n");
                VERBOSE_PRINT("Contains " << region->containedInstructions.size() << " instructions\n");
                VERBOSE_PRINT("Preceded by:\n");
                for (nDRFRegion * pred : region->precedingNDRFs) {
                    VERBOSE_PRINT("nDRF " << pred->ID << "\n");
                }
                VERBOSE_PRINT("Followed by:\n");
                for (nDRFRegion * follow : region->precedingNDRFs) {
                    VERBOSE_PRINT("nDRF " << follow->ID << "\n");
                }
            }
        }

        //bit hackish. Used to replace pointers to old regions with pointers to the regions they were merged into
        map<xDRFRegion*,xDRFRegion*> translation;
        void consolidateXDRFRegions(nDRFRegion * startHere, xDRFRegion *inRegion) {
            while (translation.count(inRegion) != 0) {
                assert(translation[inRegion] != inRegion && "Region merged into itself");
                inRegion = translation[inRegion];
            }
            VERBOSE_PRINT("Continuing xDRF region " << inRegion->ID << " towards nDRF region " << startHere->ID << "\n");
            //We will always add the following nDRFs preceding instructions to us
            SmallPtrSet<Instruction*,128> predinsts = startHere->getPrecedingInsts();
            inRegion->containedInstructions.insert(predinsts.begin(),
                                                   predinsts.end());
            for (auto region : xDRFRegions) {
                DEBUG_PRINT("Region contains:\n");
                DEBUG_PRINT("Following:");
                for (auto reg : region->followingNDRFs)
                    DEBUG_PRINT(reg->ID << "\n");
                DEBUG_PRINT("Enclave:");
                for (auto reg : region->enclaveNDRFs)
                    DEBUG_PRINT(reg->ID << "\n");
                if (region->followingNDRFs.count(startHere) != 0 || region->enclaveNDRFs.count(startHere) != 0) {
                    //Already handled case
                    if (region == inRegion)
                        return;
                    //Tomerge case
                    VERBOSE_PRINT("Merged xDRF " << inRegion->ID << " into xDRF " << region->ID << "\n");
                    region->followingNDRFs.insert(inRegion->followingNDRFs.begin(),
                                                    inRegion->followingNDRFs.end());
                    region->precedingNDRFs.insert(inRegion->precedingNDRFs.begin(),
                                                    inRegion->precedingNDRFs.end());
                    region->enclaveNDRFs.insert(inRegion->enclaveNDRFs.begin(),
                                                  inRegion->enclaveNDRFs.end());
                    region->conflictsTowardsXDRF.insert(inRegion->conflictsTowardsXDRF.begin(),
                                                          inRegion->conflictsTowardsXDRF.end());       
                    region->conflictsTowardsNDRF.insert(inRegion->conflictsTowardsNDRF.begin(),
                                                          inRegion->conflictsTowardsNDRF.end());
                    delete(inRegion);
                    translation[inRegion]=region;
                    xDRFRegions.erase(inRegion);
                    inRegion=region;
                    return;
                }
            }


            if (startHere->enclave) {
                VERBOSE_PRINT("Was enclave, added to enclave regions\n");
                inRegion->enclaveNDRFs.insert(startHere);
            } else {
                //Create a new xDRF region, and consolidate the areas following the following nDRFs
                //Also set up the preceding/following dynamics
                VERBOSE_PRINT("Was non-enclave, new xDRF region started\n");
                xDRFRegion * newXDRF = new xDRFRegion;
                xDRFRegions.insert(newXDRF);
                inRegion->followingNDRFs.insert(startHere);
                newXDRF->precedingNDRFs.insert(startHere);
                for (pair<Instruction*,Instruction*> conflict : startHere->conflictsBetweenDRF) {
                    inRegion->conflictsTowardsXDRF.insert(make_tuple(conflict.first,startHere,conflict.second));
                    newXDRF->conflictsTowardsXDRF.insert(make_tuple(conflict.first,startHere,conflict.second));
                }
                for (pair<Instruction*,pair<nDRFRegion*,Instruction*> > conflict : startHere->conflictsTowardsDRF) {
                    inRegion->conflictsTowardsNDRF.insert(make_pair(make_pair(startHere,conflict.first),make_pair(conflict.second.first,conflict.second.second)));
                    newXDRF->conflictsTowardsNDRF.insert(make_pair(make_pair(startHere,conflict.first),make_pair(conflict.second.first,conflict.second.second)));
                }
                inRegion=newXDRF;
            }

            for (nDRFRegion * followRegion : startHere->followingRegions) {
                while (translation.count(inRegion) != 0) {
                    assert(translation[inRegion] != inRegion && "Region merged into itself");
                    inRegion = translation[inRegion];
                }
                if (followRegion) 
                    consolidateXDRFRegions(followRegion,inRegion);
                else {
                    //Followed by context end, just add the following insts
                    SmallPtrSet<Instruction*,128> followinsts = startHere->getFollowingInsts();
                    inRegion->containedInstructions.insert(followinsts.begin(),
                                                           followinsts.end());
                }
            }

        }

        //Some convenience functions to make interfacing easier:

        //Obtain the XDRF region of an instruction, or NULL if it is in an nDRF region
        xDRFRegion* getXDRFRegionOfInstruction(Instruction *inst) {
            for (xDRFRegion * region: xDRFRegions)
                if (region->containedInstructions.count(inst) != 0)
                    return region;
            return NULL;
        }

        //Obtain the nDRF region of an instruction, or NULL if it is in an xDRF region
        nDRFRegion* getNDRFRegionOfInstruction(Instruction *inst) {
            for (nDRFRegion * region: nDRFRegions)
                if (region->containedInstructions.count(inst) != 0)
                    return region;
            return NULL;
        }
        
        //Check whether two instructions are within the same xDRF region
        bool areInSameXDRFRegion(Instruction *inst1, Instruction *inst2) {
            xDRFRegion *reg1 = getXDRFRegionOfInstruction(inst1),
                *reg2 = getXDRFRegionOfInstruction(inst2);
            return reg1 != NULL && reg1 == reg2;
        }
    };
}

char XDRFExtension::ID = 0;
//namespace llvm {
// INITIALIZE_PASS_BEGIN(XDRFExtension, "XDRFextend",
//                       "Identifies nDRF and xDRF regions", true, true)
// INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
// INITIALIZE_PASS_DEPENDENCY(SynchPointDelim)
// INITIALIZE_PASS_END(XDRFExtension, "XDRFextend",
//                     "Identifies nDRF and xDRF regions", true, true)
//}
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
