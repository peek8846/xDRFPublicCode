#ifndef _SYNCHPOINTDELIM_
#define _SYNCHPOINTDELIM_
//===- Identify Synchronization Points, DRF Paths and Critical REgions ----===//
// Analysis Compiler Pass to Identify the synchronization points, the paths between them
// and the critical regions
//===----------------------------------------------------------------------===//
// Created at 1/2 -16
// Jonatan Waern
//===----------------------------------------------------------------------===//

// #include <sstream>
#include <iostream>
#include <string>
#include <fstream>

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
#include "llvm/IR/Constants.h"
// #include "llvm/IR/IRBuilder.h"
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
// #include "llvm/IR/NoFolder.h"

//#include "../Utils/SkelUtils/CallingDAE.cpp"
//#include "../Utils/SkelUtils/MetadataInfo.h"

// #include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/TargetLibraryInfo.h"
// #include "llvm/Analysis/MemoryLocation.h"
// #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

// #include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"

#include "SynchPoint.hpp"
//#include "SynchPointDelim.hpp"
//#include "../PointerAliasing/UseChainAliasing.cpp"
#include "../PointerAliasing/AliasCombiner.cpp"

#define LIBRARYNAME "SynchPointDelim"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "SynchPointDelim: "
#define PRINT_DEBUG PRINTSTREAM << "SynchPointDelim (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE("light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

static cl::opt<string> graphOutput("g", cl::desc("Specify output dot file for synchpoint graph"),
                                   cl::value_desc("filename"));



namespace {

    //These are the functions that start critical regions:
    set<StringRef> critBeginFunctions = {"pthread_mutex_lock","sem_post","sem_wait","pthread_join"};
    //These are the functions that end critical regions:
    set<StringRef> critEndFunctions = {"pthread_mutex_unlock","sem_post","sem_wait","pthread_join"};
    //These are the functions that are 'from' in a one-way synchronization:
    set<StringRef> onewayFromFunctions = {"pthread_cond_signal",
                                          "pthread_cond_broadcast",
                                          "sem_post",
                                          "pthread_create",
                                          "pthread_join"};
    //These are the functions that are 'to' in a one-way synchronization:
    set<StringRef> onewayToFunctions = {"pthread_cond_wait",
                                        "sem_post",
                                        "pthread_create",
                                        "pthread_join"};

    set<StringRef> startThreadContextFunctions = {"pthread_create"};

    //These are the functions to treat as synchronization points;
    set<StringRef> synchFunctions = {};

    //Used to set up what arguments of synch calls should be considered
    map<StringRef,int> synchArgDummy =
        {{"pthread_mutex_lock",-1},
         {"pthread_mutex_unlock",-1},
         {"pthread_cond_signal",-1},
         {"pthread_cond_broadcast",-1},
         {"pthread_cond_wait",-1}};

    //These are the function to treat as if they spawn new
    //threads
    set<StringRef> threadFunctions = {"pthread_create"};
    
    struct SynchPointDelim : public ModulePass {
        static char ID;
        SynchPointDelim() : ModulePass(ID) {
            //initializeSynchPointDelimPass(*PassRegistry::getPassRegistry())
            synchFunctions.insert(critBeginFunctions.begin(),
                                  critBeginFunctions.end());
            synchFunctions.insert(critEndFunctions.begin(),
                                  critEndFunctions.end());
            synchFunctions.insert(onewayFromFunctions.begin(),
                                  onewayFromFunctions.end());
            synchFunctions.insert(onewayToFunctions.begin(),
                                  onewayToFunctions.end());
            synchFunctions.insert(startThreadContextFunctions.begin(),
                                  startThreadContextFunctions.end());
        }
        
        //Manually free the data structures left over to be used by other passes
        ~SynchPointDelim() {
            for (SynchronizationPoint* ptr : synchronizationPoints)
                delete ptr;
            for (SynchronizationVariable* ptr : synchronizationVariables)
                delete ptr;
            for (CriticalRegion* ptr : criticalRegions)
                delete ptr;
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            AU.addRequired<AAResultsWrapperPass>();
            AU.addRequired<AssumptionCacheTracker>();
            AU.addRequired<TargetLibraryInfoWrapperPass>();
            AU.setPreservesAll();
        }
    
        Module *wM;
    
        //The main runOnModule function is divided in two parts
        //The first part finds synchronization points and the drf paths between
        //them
        //The second part determines which synchronization points synch with
        //eachother
        virtual bool runOnModule(Module &M) {
            //Functions that may be the entry point of functions
            SmallPtrSet<Function*,4> entrypoints;

            wM=&M;
            aacombined = new AliasCombiner(&M,true,this,PartialAlias);
            //aacombined->addAliasResult(&aa);
            
            //Find what functions use synchronizations, this can optimize searching later
            determineSynchronizedFunctions();
            
            for (Function * fun : synchronizedFunctions) {
                VERBOSE_PRINT(fun->getName() << " might synchronize\n");
            }

            //Find the "main" function
            Function *main = M.getFunction("main");
            if (!main) {
                PRINT << "No 'main' function detected, considering manually inputing the entry function\n";
                PRINT << "Exiting\n";
                assert(!"Did not detect main function");  
            }
            entrypoints.insert(main);

            //Find other functions to analyze
            findEntryPoints(M,entrypoints);

            //Analyze each entry point
            for (Function *target : entrypoints) {
                VERBOSE_PRINT("Starting an analysis from fun: " << target->getName() << "...\n");
                //Start a delimitation of each targeted function with a dummy state,
                //starting from a NULL synch point
                vector<State> endingPoints;
                delimitFunction(target);
                for (State state : delimitFunctionDynamic[target].trailingStates) {
                    updateSynchPointWithState(state,NULL);
                }
                
                SmallPtrSet<State*,4> toDelete;
                for (pair<BasicBlock* const,SmallPtrSet<State*,2> > &bb : visitedBlocks) {
                    for (State* state : bb.second)
                        toDelete.insert(state);
                }
                for (State *state : toDelete)
                    delete state;
                visitedBlocks.clear();
            }


            //Determine what synchronization variables we have
            determineSynchronizationVariables();

            //Clean up instructions outside parallel regions
            for (Function *target : entrypoints) {
                if (target!=M.getFunction("main"))
                    for (State funState : delimitFunctionDynamic[target].leadingReverseStates) {
                        colorSynchPoints(funState.lastSynch);
                    }
            }

            // VERBOSE_PRINT("Coloreds:\n");
            // for (SynchronizationPoint *synchPoint : coloredSynchs) {
            //     if (synchPoint)
            //         VERBOSE_PRINT(synchPoint->ID << "\n");
            // }
            
            for (SynchronizationPoint *synchPoint : synchronizationPoints) {
                SmallPtrSet<Function*,1> calledFuns = getCalledFuns(synchPoint->val);
                if (anyFunctionNameInSet(calledFuns,startThreadContextFunctions))
                    colorSynchPoints(synchPoint);
            }

            cleanSynchPoints();
            
            //Determine the critical regions we have
            determineCriticalRegions(entrypoints);

            //Print Synchpointgraph
            printSynchPointGraph(entrypoints);

            //Print the info
            printInfo();
            
            clearAnalysisHelpStructures();

            return false; //Pure analysis, should not change any code
        }

        //These data structures are the results of the analysis
        SmallPtrSet<SynchronizationPoint*,32> synchronizationPoints;
        SmallPtrSet<SynchronizationVariable*,8> synchronizationVariables;
        SmallPtrSet<CriticalRegion*,8> criticalRegions;

        // SynchPointResults getResults() {
        //     SynchPointResults results;
        //     results.synchronizationPoints=synchronizationPoints;
        //     results.synchronizationVariables=synchronizationVariables;
        //     results.criticalRegions=criticalRegions;
        //     return results;
        // }

    private:

        void clearAnalysisHelpStructures() {
            delimitFunctionDynamic.clear();
            synchronizedFunctions.clear();
            getExecutableInstsDynamic.clear();
            delete aacombined;
        }

        AliasCombiner *aacombined;
        
        //The state tracks the DFS of the program flow
        //Contains the most recent synch point tracked on this path
        //Contains the instructions executable since passing that
        //synch point
        class State {
        public:
            SynchronizationPoint* lastSynch;
            SmallPtrSet<Instruction*,32> precedingInstructions;
        };

        class FunctionAnalysisState {
        public:
            enum AnalysisState {Analyzed, BeingAnalyzed};
            AnalysisState astate = BeingAnalyzed;
            vector<State> trailingStates;
            vector<State> leadingReverseStates;
            SmallPtrSet<SynchronizationPoint*,1> recursiveDummySyncs;
        };

        //Maps functions to their analysis state
        map<Function*,FunctionAnalysisState> delimitFunctionDynamic; 

        //Delimits synchronization points for a particular function
        //Input: Function to analyze and the states to track before analysing,
        // also the set of function calls that should not be analyzed
        //Returns: A set of set of states, one state for each exit point
        //and each path to reach that exit point
        //Side-effects: Updates all the synchronization points within the
        //function correctly
        void delimitFunction(Function *start) {//,vector<State> states) {
            set<CallSite> noRecurseSet;
            //return delimitFunction(start,states,noRecurseSet,CallSite());
            delimitFunction(start,noRecurseSet,CallSite());
        }

        void delimitFunction(Function *start, set<CallSite> &noRecurseSet, CallSite callInst) {
            LIGHT_PRINT("Starting analysis of function: " << start->getName() << "\n");
            if (isNotNull(callInst))
                DEBUG_PRINT("From function call: " << *(callInst.getInstruction()) << "\n");
            //Check if we have handled this function previously, if so. Do nothing
            if (delimitFunctionDynamic.count(start) != 0 &&
                delimitFunctionDynamic[start].astate == FunctionAnalysisState::Analyzed) {
                DEBUG_PRINT("Previously handled - dynamic resolution\n");
            } else {
                bool isOriginalCall=true;
                if (delimitFunctionDynamic.count(start) != 0 && delimitFunctionDynamic[start].astate == FunctionAnalysisState::BeingAnalyzed) {
                    DEBUG_PRINT("Encountered recursion - added to no-recurse set\n");
                    if (isNotNull(callInst))
                        noRecurseSet.insert(callInst);
                    isOriginalCall=false;
                }
                                
                //Start analysis of the function
                FunctionAnalysisState funState;
                funState.astate = FunctionAnalysisState::BeingAnalyzed;
                if (delimitFunctionDynamic.count(start) == 0) {
                    delimitFunctionDynamic[start]=funState;
                }
                State dummyState;
                dummyState.lastSynch = NULL;
                vector<State> trailStates;
                
                //Analyze CFG of function if it might synchronize
                if (synchronizedFunctions.count(start) != 0) {
                    //if (true) {
                    vector<State> dummyVector;
                    dummyVector.push_back(dummyState);
                    //VERBOSE_PRINT("Analyzing the CFG of " << start->getName() << "...\n");
                    trailStates = delimitFromBlock(&(start->getEntryBlock()),dummyVector,
                                                   start,
                                                   noRecurseSet);
                    //VERBOSE_PRINT("Done analyzing the CFG of " << start->getName() << "\n");
                }
                //Otherwise, just add all the instructions executable within it or functions it calls
                else {
                    DEBUG_PRINT("Resolved as non-synchronized function\n");
                    SmallPtrSet<Instruction*,128> returned = getExecutableInsts(start);
                    dummyState.precedingInstructions.insert(returned.begin(),returned.end());
                    trailStates.push_back(dummyState);
                }
                if (isOriginalCall==true) {
                    LIGHT_PRINT("Original analysis call is done\n");
                    delimitFunctionDynamic[start].astate = FunctionAnalysisState::Analyzed;
                    delimitFunctionDynamic[start].leadingReverseStates=unifyRedundantStates(delimitFunctionDynamic[start].leadingReverseStates);
                    LIGHT_PRINT("Clearing out the shortcut data structures\n");
                    //Clean out the tracked basicblocks from the visited and shortcircuited sets
                    SmallPtrSet<State*,4> toDelete;
                    for (Function::iterator block_it = start->begin(); block_it != start->end(); ++block_it) {
                        BasicBlock* block = &*block_it;
                        if (visitedBlocks.count(block) != 0) {
                            for (State *ptr : visitedBlocks[block])
                                toDelete.insert(ptr);
                            visitedBlocks.erase(block);
                        }
                        speccCaseBackedgeBlocks.erase(block);
                    }
                    for (State *state : toDelete)
                        delete state;

                    delimitFunctionDynamic[start].trailingStates.insert(delimitFunctionDynamic[start].trailingStates.end(),
                                                                        trailStates.begin(),
                                                                        trailStates.end());
                    delimitFunctionDynamic[start].trailingStates=unifyRedundantStates(delimitFunctionDynamic[start].trailingStates);

                    //Handle the left-over recursive states, if any
                    LIGHT_PRINT("Handling recursive dummy syncs, if any\n");

                    for (SynchronizationPoint *dummy : delimitFunctionDynamic[start].recursiveDummySyncs) {
                        for (pair<Function* const, FunctionAnalysisState> & funstatepair : delimitFunctionDynamic) {
                            FunctionAnalysisState &funstate=funstatepair.second;
                            for (vector<State>::iterator it = funstate.trailingStates.begin();
                                 it != funstate.trailingStates.end();) {
                                if (it->lastSynch == dummy)
                                    it=funstate.trailingStates.erase(it);
                                else
                                    it++;
                            }
                        }

                        for (SynchronizationPoint* toPoint : dummy->following) {
                            if (toPoint) {
                                State newState;
                                //Update so that the trailing states have as followers the states found from the
                                //dumy, and vice-verse
                                for (State state : delimitFunctionDynamic[start].trailingStates) {
                                    state.precedingInstructions.insert(dummy->followingInsts[toPoint].begin(),
                                                                       dummy->followingInsts[toPoint].end());
                                    updateSynchPointWithState(state,toPoint);
                                }
                                //Update so that the following states of the dummy no long have the dummy as preceding
                                toPoint->preceding.erase(dummy);
                                toPoint->precedingInsts.erase(dummy);
                            }
                        }
                    }
                    for (SynchronizationPoint *dummy : delimitFunctionDynamic[start].recursiveDummySyncs) {
                        delete dummy;
                    }
                    delimitFunctionDynamic[start].recursiveDummySyncs.clear();

                    LIGHT_PRINT("Done.\n");
                } else {
                    LIGHT_PRINT("Setting up dummy state for recursive call\n");
                    SynchronizationPoint * dummySync = new SynchronizationPoint;
                    State newState;
                    newState.lastSynch=dummySync;
                    delimitFunctionDynamic[start].recursiveDummySyncs.insert(dummySync);
                    delimitFunctionDynamic[start].trailingStates.push_back(newState);
                }

                assert(!(delimitFunctionDynamic[start].trailingStates.size() == 0 && start != wM->getFunction("main")) && "Empty trailing states in function that has finished analysis that is not main.");
            }
            DEBUG_PRINT("Done analyzing " << start->getName() << "\n");
        }

#define HASMORETHANONEPRED(ptr) (ptr->getUniquePredecessor() == NULL && pred_begin(ptr) != pred_end(ptr))

        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states,
                                       //vector<State> *firstReachable,
                                       Function *addFirstToFun,
                                       set<CallSite> &noRecurseSet) {
            map<BasicBlock*,SmallPtrSet<Instruction*,64> > dummy1;
            map<BasicBlock*,SmallPtrSet<BasicBlock*,64> > dummy2;
            return delimitFromBlock(curr,states,addFirstToFun,noRecurseSet,
                                    SmallPtrSet<BasicBlock*,64>(),
                                    dummy1,dummy2);
        }

        //Maps basicblocks to reversestates
        map<BasicBlock*,SmallPtrSet<State*,2> > visitedBlocks;

        //Maps basicblocks to states that need continuation
        map<BasicBlock*,vector<State> > speccCaseBackedgeBlocks;


        //Delimits synchronization points starting with the specified block
        //Input: Block to start at and The state before analyzing, as well
        //as the set to store the first encountered synch points in
        //(if null, they are not stored). Also takes the block this search
        //branched from, if any
        //Returns: A set of states, one for each end point of the search
        //Side-effects: Updates the synchronization point variables
        //with the paths discoverable from this basic block
        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states,
                                       Function* addFirstToFun,
                                       set<CallSite> &noRecurseSet,
                                       SmallPtrSet<BasicBlock*,64> previousBlocks,
                                       map<BasicBlock*,SmallPtrSet<Instruction*,64> > &backAddedInsts,
                                       map<BasicBlock*,SmallPtrSet<BasicBlock*,64> > &backAddedBlocks) {
            //DEBUG_PRINT("Started a new search branch from BasicBlock: "<< curr->getName() << "\n");

            states=unifyRedundantStates(states);

            map<BasicBlock*,SmallPtrSet<Instruction*,64> > backAddedInstsLocal;
            map<BasicBlock*,SmallPtrSet<BasicBlock*,64> > backAddedBlocksLocal;
            
            //This is the set of states of sub-branches that we need to keep
            //track of. These will be returned together with the states
            //obtained in the current search once we return
            vector<State> finishedSearchStates;
            
            while (curr) {
                LIGHT_PRINT("Handling BasicBlock: " << curr->getName() << "\n");
                // DEBUG_PRINT("Previously finished basicblocks are:\n");
                // for (pair<BasicBlock* const,SmallPtrSet<State*,2> > &bb : visitedBlocks)
                //     DEBUG_PRINT("  " << bb.first->getName() << "\n");
                // DEBUG_PRINT("Previously visited blocks on this branch are:\n");
                // for (BasicBlock* bb : previousBlocks)
                //     DEBUG_PRINT("  " << bb->getName() << "\n");
                // DEBUG_PRINT("Most recently visited synch points are:\n");
                // for (State state : states)
                //     if (state.lastSynch)
                //         DEBUG_PRINT("  " << state.lastSynch->ID << "\n");
                //     else
                //         DEBUG_PRINT("  context begin\n");

                // DEBUG_PRINT("States are:\n");
                // for (State state : states) {
                //     if (state.lastSynch != NULL) {
                //         DEBUG_PRINT("  From synchpoint " << state.lastSynch->ID << "\n");
                //     } else {
                //         DEBUG_PRINT("  From context begin\n");
                //     }
                //     DEBUG_PRINT("     " << state.precedingInstructions.size() << " instructions\n");
                //     // for (Instruction * inst : state.precedingInstructions) {
                //     //     DEBUG_PRINT("   " << *inst << "\n");
                //     // }
                // }
                
                //If this is true, don't search further
                bool shortcut=false;

                //Backedge case
                if (previousBlocks.count(curr) != 0) {
                    LIGHT_PRINT("Search stopped in block: " << curr->getName() << " due to backedge\n");
                    for (State state : states) {
                        auto prev = backAddedInsts[curr];
                        prev.insert(state.precedingInstructions.begin(),
                                    state.precedingInstructions.end());
                        backAddedInsts[curr]=prev;
                    }
                    auto prev = backAddedBlocks[curr];
                    prev.insert(previousBlocks.begin(),
                                previousBlocks.end());
                    backAddedBlocks[curr]=prev;
                    // //Should not need to return anything extra
                    // curr=NULL;
                    // continue;
                    shortcut=true;
                }
                //Forward-edge case || Back-edge case across synch points
                if (visitedBlocks.count(curr) != 0) {
                    LIGHT_PRINT("Search stopped in block: " << curr->getName() << " due to forwardedge or backedge across basicblocks\n");
                    //We know this path must be completed, thus we simply check
                    //the mapping and find the reverse states from here

                    bool clearFirstReachable=false;

                    for (State state_ : states) {
                        //DEBUG_PRINT("Fast-forwarding a state...\n");
                        speccCaseBackedgeBlocks[curr].push_back(state_);
                        for (State *state : visitedBlocks[curr]) {
                            state_.precedingInstructions.insert(state->precedingInstructions.begin(),
                                                                state->precedingInstructions.end());
                            updateSynchPointWithState(state_,state->lastSynch);
                            //If the state reaches context end, return it

                            //Toss the synchpoint upwards if we should
                            if (addFirstToFun && state->lastSynch != NULL) {
                                clearFirstReachable=true;
                                State state__;
                                state__.precedingInstructions=state_.precedingInstructions;
                                state__.lastSynch=state->lastSynch;
                                //LIGHT_PRINT("Added " << state__.lastSynch->ID << " as first reachable in fun " << addFirstToFun->getName() << "(fast-forward)\n");
                                delimitFunctionDynamic[addFirstToFun].leadingReverseStates.push_back(state__);
                            }
                            
                            if (state->lastSynch == NULL) {
                                finishedSearchStates.push_back(state_);
                            }
                        }
                        speccCaseBackedgeBlocks[curr]=unifyRedundantStates(speccCaseBackedgeBlocks[curr]);
                    }
                    if (clearFirstReachable)
                        addFirstToFun=NULL;
                    // curr=NULL;
                    // continue;
                    shortcut=true;
                }

                if (shortcut) {
                    //LIGHT_PRINT("Ended this branch of search\n");
                    curr=NULL;
                    continue;
                }
                    

                previousBlocks.insert(curr);

                //Analyze the current block
                for (BasicBlock::iterator currb_it=curr->begin(),
                         curre=curr->end();
                     currb_it != curre; ++currb_it) {
                    Instruction *currb=&*currb_it;
                    // if (!(allHandledInsts.insert(&*currb).second)) {
                    //     // DEBUG_PRINT("Instruction was: " << *currb << "\nin basic block: " << curr->getName() << "\n");
                    //     assert("Handled the same instruction twice!");
                    // }
  
                    // DEBUG_PRINT("Handled instruction: " << *currb << "\n");

                    //Special case: end search branch at unreachable instruction
                    if (isa<UnreachableInst>(currb)) {
                        DEBUG_PRINT("Terminated search due to unreachable instruction\n");
                        // for (BasicBlock* block : previousBlocks) {
                        //     for (State state : states) {
                        //         State* newState = new State;
                        //         newState->lastSynch=NULL;
                        //         newState->precedingInstructions=state.precedingInstructions;
                        //         visitedBlocks[block].insert(newState);
                        //     }
                        // }
                                
                        curr=NULL;
                        break;
                    }
                  
                    if (isSynch(currb)) {
                        //Handle synchronization point
                        //See if we've already visited this point
                        // DEBUG_PRINT("Visited instruction that is synch point: " << *currb << "\n");
                        SynchronizationPoint *synchPoint = findSynchPoint(synchronizationPoints,currb);
                        bool visited = true;
                        if (!synchPoint) {
                            visited = false;
                            //DEBUG_PRINT("Was not previously visited\n");
                            //If not, create a new synchronization point
                            synchPoint = new SynchronizationPoint;
                            LIGHT_PRINT("Created synch point ID: " << synchPoint->ID << " : " << *currb << "\n");
                            synchPoint->val=currb;
                            synchronizationPoints.insert(synchPoint);
                            SmallPtrSet<Function*,1> calledFuns = getCalledFuns(currb);
                            if (anyFunctionNameInSet(calledFuns,critBeginFunctions))
                                synchPoint->isCritBegin=true;
                            if (anyFunctionNameInSet(calledFuns,critEndFunctions))
                                synchPoint->isCritEnd=true;
                            if (anyFunctionNameInSet(calledFuns,onewayFromFunctions))
                                synchPoint->isOnewayFrom=true;
                            if (anyFunctionNameInSet(calledFuns,onewayToFunctions))
                                synchPoint->isOnewayTo=true;                            
                        }
                        //Toss the synchpoint upwards if we should
                        if (addFirstToFun) {
                            //Only do this once, we only need to pass
                            //the first synchpoints we encounter
                            State newState;
                            newState.lastSynch = synchPoint;
                            //We might have several states, but we should only
                            //have a single synchPoint
                            for (State state : states) {
                                newState.precedingInstructions.insert(state.precedingInstructions.begin(),
                                                                      state.precedingInstructions.end());
                            }
                            //LIGHT_PRINT("Added " << newState.lastSynch->ID << " as first reachable in fun(plain)" << addFirstToFun->getName() << "\n");
                            delimitFunctionDynamic[addFirstToFun].leadingReverseStates.push_back(newState);
                            //addFirstToFun->push_back(newState);
                            addFirstToFun=NULL;
                        }
                        //Perform updates
                        for (State &state : states) {
                            updateSynchPointWithState(state,synchPoint);
                        }

                        //Update previous basicblocks to shortcut searches through them
                        for (BasicBlock* block : previousBlocks) {
                            if (HASMORETHANONEPRED(block)) {
                                //DEBUG_PRINT("Added BB " << block->getName() << " having the follower Synchpoint " << synchPoint->ID << "\n");
                                for (State state : states) {
                                    State* newState = new State;
                                    newState->lastSynch=synchPoint;
                                    newState->precedingInstructions=state.precedingInstructions;
                                    visitedBlocks[block].insert(newState);
                                }
                            }
                        }

                        //Clear previous states, all searched paths end here
                        states.clear();

                        //If we're not the first one here, then someone else
                        //has already taken care of all the following
                        //paths and we need not continue
                        if (visited) {
                            //Return nothing, everything is already handled
                            //by previous searches
                            return vector<State>();
                        } else {
                            //Start a new path
                            State newState;
                            newState.lastSynch=synchPoint;
                            states.push_back(newState);
                            backAddedInstsLocal.clear();
                            backAddedBlocksLocal.clear();
                            previousBlocks.clear();
                        }
                    } else {
                        //If the instruction is a call, figure out which
                        //function it is
                        if (isCallSite(currb)) {
                            SmallPtrSet<Function*,1> calledFuns = getCalledFuns(currb);
                            LIGHT_PRINT(calledFuns.size() << " functions could be called\n");
                            for (Function* calledFun : calledFuns) {
                                LIGHT_PRINT("Handling " << calledFun->getName() << "\n");
                                //Don't recurse on this function call
                                if (noRecurseSet.count(CallSite(currb)) != 0) {
                                    // DEBUG_PRINT("DFS path ended in BasicBlock: " << curr->getName() << " due to already processed recursive call\n");
                                    // curr = NULL;
                                    // continue;
                                } else if (!calledFun->empty()) {
                                    //Parse the function and obtain the states
                                    //that are at the exit of the function
                                    // LIGHT_PRINT("Analysing CG of " << calledFun->getName() << "\n");
                                    delimitFunction(calledFun,noRecurseSet,CallSite(currb));
                                    //Update the synch points that are accessible from the
                                    //entry of the function such that their preceding paths
                                    //contain the current preceding paths
                                    //DEBUG_PRINT("Function analysis of "<< start->getName()<< " done, updating states and synch points\n");
                                    //DEBUG_PRINT("Cross size is: " << delimitFunctionDynamic[start].leadingReverseStates.size() << "x"
                                    //            << states.size() << "\n");
                                    states=unifyRedundantStates(states);
                                    // LIGHT_PRINT("Updating current states with states from call to " << calledFun->getName() << "\n");
                                    // LIGHT_PRINT("Sizes are: " << states.size() << " x " << delimitFunctionDynamic[calledFun].leadingReverseStates.size() << "\n");
                                    for (State leadState : delimitFunctionDynamic[calledFun].leadingReverseStates) {
                                        if (leadState.lastSynch != NULL) {
                                            //DEBUG_PRINT("Updating with leading synchpoint:" << leadState.lastSynch->ID << "\n");
                                            
                                            for (State state : states) {
                                                state.precedingInstructions.insert(leadState.precedingInstructions.begin(),
                                                                                   leadState.precedingInstructions.end());
                                                updateSynchPointWithState(state,leadState.lastSynch);
                                                
                                                State* newState = new State;
                                                newState->lastSynch=leadState.lastSynch;
                                                newState->precedingInstructions=state.precedingInstructions;
                                                
                                                if (addFirstToFun && addFirstToFun != calledFun) {
                                                    //LIGHT_PRINT("Added " << newState->lastSynch->ID << " as first reachable in fun " << addFirstToFun->getName() << "(encountered in function call)\n");
                                                    delimitFunctionDynamic[addFirstToFun].leadingReverseStates.push_back(*newState);
                                                }
                                                
                                                bool wasAdded=false;

                                                //Update previous basicblocks to shortcut searches through them
                                                for (BasicBlock* block : previousBlocks) {
                                                    if (HASMORETHANONEPRED(block)) {
                                                        //DEBUG_PRINT("Added BB " << block->getName() << " having the follower Synchpoint " << leadState.lastSynch->ID << "\n");
                                                        wasAdded=true;
                                                        visitedBlocks[block].insert(newState);
                                                    }
                                                }
                                                if (!wasAdded)
                                                    delete newState;
                                            }
                                        }    
                                    }
                                        
                                    bool clearPrevious=true;
                                    vector<State> newStates;

                                    // DEBUG_PRINT("Updates done, setup return:\n");
                                    // DEBUG_PRINT("Cross size is: " << delimitFunctionDynamic[start].trailingStates.size() << "x("
                                    //             << states.size() << ")\n");
                                    //DEBUG_PRINT("Setting up new states to use after call...\n");
                                    for (State trailState : delimitFunctionDynamic[calledFun].trailingStates) {
                                        
                                        if (trailState.lastSynch != NULL) {
                                            //DEBUG_PRINT("Added state from synch point:" << trailState.lastSynch->ID << "\n");
                                            newStates.push_back(trailState);
                                        } else {
                                            //DEBUG_PRINT("Continued states that existed before call due to call having a path with no synch points\n");
                                            //Edge case, there is no synch point on this path through the
                                            //function, we need to add the instructions encountered
                                            //to the preceding states
                                            //and return accordingly
                                            clearPrevious=false;
                                            for (State state : states) {
                                                state.precedingInstructions.insert(trailState.precedingInstructions.begin(),
                                                                                   trailState.precedingInstructions.end());
                                                newStates.push_back(state);
                                            }
                                        }
                                    }

                                    if (clearPrevious) {
                                        previousBlocks.clear();
                                        addFirstToFun = NULL;
                                    }

                                    states=newStates;
                                                                        
                                } else {
                                    //DEBUG_PRINT("Added " << calledFun->getName() << " as an analyzed instruction due to it having no function body\n");
                                    for (State &state : states) {
                                        state.precedingInstructions.insert(currb);
                                    }
                                }
                                //Continue analysis as usual with those states
                            }
                            if (calledFuns.size() == 0) {
                                //We failed to determine which function could
                                //be called, print an error about this
                                VERBOSE_PRINT("Failed to determine the function called by: " << *currb << ", ignoring the error\n");
                            }
                        }
                        else {
                            //Otherwise, simply add the instruction to the
                            //states we're tracking
                            if (isa<StoreInst>(currb) || isa<LoadInst>(currb)) {
                                for (State &state : states) {
                                    state.precedingInstructions.insert(currb);
                                }
                            }
                        }
                    }
                }
                if (!curr)
                    continue;

                succ_iterator
                    bb = succ_begin(curr),
                    bbe = succ_end(curr);
                
                if (curr->getSingleSuccessor())
                    curr = curr->getSingleSuccessor();
                else {
                    if (bb == bbe) {
                        //LIGHT_PRINT("Search ended in " << curr->getName() << " due to no successing blocks\n");
                        //Update previous basicblocks to shortcut searches through them
                        for (BasicBlock* block : previousBlocks) {
                            //DEBUG_PRINT("Added BB " << block->getName() << " being followed by context end\n");
                            for (State state : states) {
                                State* newState = new State;
                                newState->lastSynch=NULL;
                                newState->precedingInstructions=state.precedingInstructions;
                                visitedBlocks[block].insert(newState);
                            }
                        }

                        finishedSearchStates.insert(finishedSearchStates.end(),
                                                    states.begin(),states.end());
                        curr=NULL;
                        continue;
                    } else {
                        for (;bb != bbe; ++bb) {
                            states.insert(states.end(),
                                          speccCaseBackedgeBlocks[curr].begin(),
                                          speccCaseBackedgeBlocks[curr].end());
                            states=unifyRedundantStates(states);
                            succ_iterator cheap_tricks = bb;
                            if (++cheap_tricks == bbe) {
                                curr = *bb;
                                continue;
                            }
                            LIGHT_PRINT("Branching from BB: " << curr->getName() << ", previousblocks size is " << previousBlocks.size() << "\n");
                            vector<State> resultStates = delimitFromBlock(*bb,states,addFirstToFun,noRecurseSet,previousBlocks,backAddedInstsLocal,backAddedBlocksLocal);
                            LIGHT_PRINT("Completed a branch from  BB: " << curr->getName() << "\n");
                            //All instructions we got back must be added as preceding to all our current
                            //states, and also our parents
                            for (auto backadd : backAddedInstsLocal) {
                                if (previousBlocks.count(backadd.first) != 0) {
                                    backAddedInsts.insert(backadd);
                                }
                            }

                            for (State &state : states) {
                                int totaladded=0;
                                for (auto backadd : backAddedInsts) {
                                    totaladded+=backadd.second.size();
                                    state.precedingInstructions.insert(backadd.second.begin(),
                                                                       backadd.second.end());
                                }
                                DEBUG_PRINT("While handling backaddedinsts, added " << totaladded << " instructions through special backedge cases\n");
                            }

                            finishedSearchStates.insert(finishedSearchStates.end(),
                                                        resultStates.begin(),resultStates.end());
                            //Similarly, all the blocks we got back must be tracked by us and our parents
                            for (auto backadd : backAddedBlocksLocal) {
                                if (previousBlocks.count(backadd.first) != 0) {
                                    backAddedBlocks.insert(backadd);
                                    previousBlocks.insert(backadd.second.begin(),
                                                          backadd.second.end());
                                }
                            }
                        }
                    }    
                }
            }
            // finishedSearchStates.insert(finishedSearchStates.end(),
            //                             states.begin(),states.end());
            unifyRedundantStates(finishedSearchStates);
            return finishedSearchStates;
        }

        //Less verbose than printInfo
        void print(raw_ostream &O,const Module *M) const {
            O << "SynchPointDelim: Found " << synchronizationPoints.size() << " synchronization points\n";
            O << "SynchPointDelim: Grouped these into " << synchronizationVariables.size() << " synchronization variables\n";
            O << "SynchPointDelim: Found " << criticalRegions.size() << " critical regions\n";
        }


#define PRINTSYNC(ptr) ptr->ID << (ptr->isCritBegin ? string(" : Acq") : string("")) << (ptr->isCritEnd ? string(" : Rel") : string(""))

        void printSynchPointGraph(SmallPtrSet<Function*,4> entryPoints) {
            ofstream outputGraph(graphOutput.c_str());
            if (outputGraph.is_open()) {
                outputGraph << "digraph \"" << (wM->getName().data()) << " Synchpoint Graph\" {\n";
                for (CriticalRegion * region : criticalRegions) {
                    for (SynchronizationPoint * synchPoint : region->entrySynchPoints) {
                        outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" [label=\"" << synchPoint->ID << " begins " << region->ID << "\"];\n";
                        outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" [shape=box];\n";
                    }
                    for (SynchronizationPoint * synchPoint : region->exitSynchPoints) {
                        outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" [label=\"" << synchPoint->ID << " ends " << region->ID << "\"];\n";
                        outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" [shape=box];\n";
                    }
                }

                for (SynchronizationPoint *synchPoint : synchronizationPoints) {
                    for (SynchronizationPoint *synchPointTo : synchPoint->following) {
                        if (synchPoint) {
                            if (synchPointTo)
                                outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" -> \"" << PRINTSYNC(synchPointTo) << "\";\n";
                            else
                                // if (entryPoints.count(synchPoint->val->getParent()->getParent()) != 0)
                                outputGraph << "\"" << PRINTSYNC(synchPoint) << "\" -> " << "\"Context End\";\n";
                        }
                    }                    
                }
                //for (Function &fun : wM->getFunctionList()) {
                for (Function *fun : entryPoints) {
                    for (State funState : delimitFunctionDynamic[fun].leadingReverseStates) {
                        if (funState.lastSynch)
                            outputGraph << "\"" << (fun->getName().data()) << " entry\" -> \"" << PRINTSYNC(funState.lastSynch) << "\";\n";
                    }
                }

                outputGraph << "}\n";
                outputGraph.close();
            } else if (graphOutput.compare("") == 0) {
                VERBOSE_PRINT("Failed to output synchpoint graph\n");
            }
        }

        //Print information about synch points and synch variables
        void printInfo() {
            VERBOSE_PRINT("Printing synchronization point info...\n");
            //Print info about synch points
            for (SynchronizationPoint* synchPoint : synchronizationPoints) {
                VERBOSE_PRINT("Synch Point: " << synchPoint->ID << "\n");
                VERBOSE_PRINT("Value: " << *(synchPoint->val) << "\n");
                if (synchPoint->isCritBegin)
                    VERBOSE_PRINT("begins a critical region\n");
                if (synchPoint->isCritEnd)
                    VERBOSE_PRINT("ends a critical region\n");
                if (synchPoint->isOnewayFrom)
                    VERBOSE_PRINT("is FROM in a one-way synchronization\n");
                if (synchPoint->isOnewayTo)
                    VERBOSE_PRINT("is TO in a one-way synchronization\n");
                VERBOSE_PRINT("Preceding:\n");
                for (SynchronizationPoint* precedingPoint : synchPoint->preceding) {
                    if (precedingPoint) {
                        VERBOSE_PRINT("ID: " << precedingPoint->ID << ", " << synchPoint->precedingInsts[precedingPoint].size() << " instructions \n");
                    } else {
                        VERBOSE_PRINT("Context start, " << synchPoint->precedingInsts[precedingPoint].size() << " instructions \n");
                    }
                    // for (auto it=synchPoint->precedingInsts[precedingPoint].begin(),
                    //          et=synchPoint->precedingInsts[precedingPoint].end();
                    //      it != et; ++it)
                    //     DEBUG_PRINT(**it << "\n");
                }
                VERBOSE_PRINT("Following:\n");
                for (SynchronizationPoint* followingPoint : synchPoint->following) {
                    if (followingPoint) {
                        VERBOSE_PRINT("ID: " << followingPoint->ID << ", " << synchPoint->followingInsts[followingPoint].size() << " instructions\n");
                    } else {
                        VERBOSE_PRINT("Context end, " << synchPoint->followingInsts[followingPoint].size() << " instructions\n");
                    }
                    // for (auto it=synchPoint->followingInsts[followingPoint].begin(),
                    //          et=synchPoint->followingInsts[followingPoint].end();
                    //      it != et; ++it)
                        //DEBUG_PRINT(**it << "\n");
                }
            }
            VERBOSE_PRINT("Printing synchronization variable info...\n");
            for (SynchronizationVariable *synchVar : synchronizationVariables) {
                VERBOSE_PRINT("Synch var: " << synchVar->ID << "\n");
                VERBOSE_PRINT("Contains: (ID|VALUE)\n");
                for (SynchronizationPoint *synchPoint : synchVar->synchronizationPoints) {
                    VERBOSE_PRINT(synchPoint->ID << " ; " << *(synchPoint->val) << "\n");
                }
            }
            VERBOSE_PRINT("Printing critical region info...\n");
            for (CriticalRegion *critRegion : criticalRegions) {
                VERBOSE_PRINT("Region: " << critRegion->ID << "\n");
                if (critRegion->firstRegionInEntry)
                    VERBOSE_PRINT("Can be first region executed by thread\n");
                VERBOSE_PRINT("  Synchronizes on:\n");
                for (SynchronizationVariable* synchVar : critRegion->synchsOn) {
                    VERBOSE_PRINT("   Synch Var: " << synchVar->ID << "\n");
                }
                VERBOSE_PRINT("  Entry points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->entrySynchPoints) {
                    VERBOSE_PRINT("   Synch Point: " << synchPoint->ID << "\n");
                }
                VERBOSE_PRINT("  Contains points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->containedSynchPoints) {
                    VERBOSE_PRINT("   Synch Point: " << synchPoint->ID << "\n");
                }
                VERBOSE_PRINT("  Exit points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->exitSynchPoints) {
                    VERBOSE_PRINT("   Synch Point: " << synchPoint->ID << "\n");
                }
            }
            
            LIGHT_PRINT("Printing function structure info...\n");
            for (Function &fun : wM->getFunctionList()) {
                if (synchronizedFunctions.count(&fun) != 0) {
                    LIGHT_PRINT("Function: " << fun.getName() << "\n");
                    LIGHT_PRINT("  Synchpoints reachable from entry:\n");
                    for (State state : delimitFunctionDynamic[&fun].leadingReverseStates) {
                        LIGHT_PRINT("    " << state.lastSynch->ID << "\n");
                    }
                    LIGHT_PRINT("  Synchpoints that reach context end:\n");
                    for (State state : delimitFunctionDynamic[&fun].trailingStates) {
                        if (state.lastSynch != NULL)
                            LIGHT_PRINT("    " << state.lastSynch->ID << "\n");
                        else
                            LIGHT_PRINT("    context begin\n");
                    }
                }
            }
        }

        //Utility: Checks wether a given callsite contains a call
        bool isNotNull(CallSite call) {
            return call.isCall() || call.isInvoke();
        }
        
        //Utility: Checks whether an instruction could be a callsite
        bool isCallSite(Instruction* inst) {
            return isNotNull(CallSite(inst));
        }

        //Obtains the set of functions that can be immediately called when
        //executing inst
        SmallPtrSet<Function*,1> getCalledFuns(Instruction *inst) {
            LIGHT_PRINT("Finding functions that can be called by " << *inst << "\n");
            SmallPtrSet<Function*,1> toReturn;
            SmallPtrSet<Value*,8> alreadyVisited;
            if (isCallSite(inst)) {
                DEBUG_PRINT("which is a callsite\n");
                CallSite call = CallSite(inst);
                Value *calledValue = call.getCalledValue();
                //Rather than doing this: would it be possible with a decent AA to just
                //check if the value aliases with each function in the module?
                deque<Value*> calledValues;
                calledValues.push_back(calledValue);
                while (!calledValues.empty()) {
                    Value *nextValue = calledValues.front();
                    calledValues.pop_front();
                    nextValue = nextValue->stripInBoundsConstantOffsets();
                    if (alreadyVisited.count(nextValue) != 0)
                        continue;
                    alreadyVisited.insert(nextValue);
                    //Try to resolve the value into a function
                    if (auto fun = dyn_cast<Function>(nextValue)) {
                        LIGHT_PRINT(fun->getName() << " could be called\n");
                        toReturn.insert(fun);
                    }
                    //Since we are dealing with functions, only a few
                    //instructions should be possible
                    else if (auto phi = dyn_cast<PHINode>(nextValue))
                        for (int i = 0; i < phi->getNumIncomingValues(); ++i)
                            calledValues.push_back(phi->getIncomingValue(i));
                    else if (dyn_cast<Instruction>(nextValue) && isCallSite(dyn_cast<Instruction>(nextValue))) {
                        //We get the return from a function, find all values
                        //that could be returned from that function
                        //and toss them onto the queue
                        //TODO: Do we need to handle the case where functions are
                        //returned recursively?
                        //For now, ignore it
                        SmallPtrSet<Function*,1> calledFuns = getCalledFuns(dyn_cast<Instruction>(nextValue));
                        for (Function* fun : calledFuns) {
                            for (auto instb = inst_begin(fun);
                                 instb != inst_end(fun); ++instb) {
                                if (auto returninst = dyn_cast<ReturnInst>(&*instb)) {
                                    if (Value* returnval = returninst->getReturnValue())
                                        calledValues.push_back(returnval);
                                }
                            }
                        }
                    }
                    
                    //Here we pick apart data structures
                    else if (auto gep = dyn_cast<GetElementPtrInst>(nextValue)) {
                        //Any remaining gep must, by definition, have a dynamic index
                        //So we just resolve the value that is gepped from
                        calledValues.push_back(gep->getPointerOperand());
                    }
                    // if (auto ext = dyn_cast<ExtractElementInst>(nextValue)) {
                    //     int index = -1;
                    //     if (auto cons = dyn_cast<Constant>(ext->getIndexOperand)) {
                    //         nextValues.push_back(ext->getVectorOperand()->
                    //     }
                    // }
                    else if (auto load = dyn_cast<LoadInst>(nextValue)) {
                        calledValues.push_back(load->getPointerOperand());
                    }
                    else if (auto arg = dyn_cast<Argument>(nextValue)) {
                        //Track values from the callsites
                        for (auto use = arg->getParent()->users().begin();
                             use != arg->getParent()->users().end();
                             ++use) {
                            if (dyn_cast<Instruction>(*use) && isCallSite(dyn_cast<Instruction>(*use))) {
                                CallSite callsite(*use);
                                calledValues.push_back(callsite.getArgOperand(arg->getArgNo()));
                            }
                        }
                    }
                    else if (auto glob = dyn_cast<GlobalVariable>(nextValue)) {
                        //at this point we can basically give up, any function
                        //that has its adress taken can be used here
                        //LIGHT_PRINT(*inst << " calls a function stored in a global, finding functions that have their address taken. Global is: " << *glob << "\n");
                        for (Function &fun : inst->getParent()->getParent()->getParent()->getFunctionList()) {
                            //LIGHT_PRINT("Considering function: " << fun.getName() << "\n");
                            if (fun.hasAddressTaken()) {
                                //LIGHT_PRINT("It has its adress taken\n");
                                if (fun.getFunctionType() == dyn_cast<FunctionType>(getTypeOfPointerType(glob->getType()))) {
                                    //LIGHT_PRINT("And the types match\n");
                                    toReturn.insert(&fun);
                                }
                            }
                        }
                    } else {
                        //We failed to resolve function to be called. Print diagnostic message
                        VERBOSE_PRINT("Failed to resolve value: " << *nextValue
                                      << "\nwhich has type: " << typeid(*nextValue).name()
                                      << "\nwhile resolving called functions.\n");
                    }                    
                }
            }
            return toReturn;
        }
        
        //Utility: Returns the proper type of a pointer type
        Type *getTypeOfPointerType(Type *ptr) {
            while (PointerType *p = dyn_cast<PointerType>(ptr))
                ptr = p->getElementType();
            return ptr;
        }

        //Utility: Returns true if a set of functions contains a function with
        //a name that is in a stringref set
        bool anyFunctionNameInSet(SmallPtrSet<Function*,1> funs,set<StringRef> stringSet) {
            for (Function* fun : funs) {
                if (stringSet.count(fun->getName()) != 0)
                    return true;
            }
            return false;
        }

        //Utility: Returns true if an instruction is a synchronization point
        bool isSynch(Instruction *inst) {
            if (!isCallSite(inst))
                return false;
            return anyFunctionNameInSet(getCalledFuns(inst),synchFunctions);
        }

        //Utility: Searches a SmallPtrSet for a SynchronizationPoint
        //with a particular instruction value
        SynchronizationPoint *findSynchPoint(SmallPtrSet<SynchronizationPoint*,32>
                                             synchSet, Instruction* inst) {
            for (SynchronizationPoint *examine : synchSet) {
                if (examine->val == inst)
                    return examine;
            }
            
            return NULL;
        }
        
        //Utility: Given a set of states, returns a set with with each unique
        //predecessor in the states
        vector<State> unifyRedundantStates(vector<State> toMerge) {
            //LIGHT_PRINT("Unifying redundant states\n");
            vector<State> result;
            map<SynchronizationPoint*,int> indexMapping;
            int nextFreeIndex = 0;
            for (State state : toMerge) {
                if (indexMapping.count(state.lastSynch) == 0) {
                    result.push_back(state);
                    indexMapping[state.lastSynch]=nextFreeIndex++;
                } else {
                    result[indexMapping[state.lastSynch]].
                        precedingInstructions.insert(state.precedingInstructions.begin(),
                                                     state.precedingInstructions.end());
                }   
            }
            //LIGHT_PRINT("Removed " << (toMerge.size() - result.size()) << " states\n");
            return result;
        }

        //Utility: Given a synch point and a state, updates both as if the
        //state leads to the synch point
        void updateSynchPointWithState(State state,SynchronizationPoint *synchPoint) {
            LIGHT_PRINT("Started an update:\n");
            LIGHT_PRINT("Preceding: ");
            if (state.lastSynch != NULL) {
                LIGHT_PRINT("Synchpoint " << state.lastSynch->ID << "\n");
                LIGHT_PRINT("Updating following instructions of syncpoint " << state.lastSynch->ID << "\n");
                LIGHT_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                state.lastSynch->following.insert(synchPoint);
                state.lastSynch->followingInsts[synchPoint].insert(state.precedingInstructions.begin(),
                                                                   state.precedingInstructions.end());
            } else {
                LIGHT_PRINT("Context begin\n");
            }
            LIGHT_PRINT("Following: ");
            if (synchPoint) {
                LIGHT_PRINT("Synchpoint " << synchPoint->ID << "\n");
                LIGHT_PRINT("Updating preceding instructions of syncpoint " << synchPoint->ID << "\n");
                LIGHT_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                synchPoint->preceding.insert(state.lastSynch);
                synchPoint->precedingInsts[state.lastSynch].insert(state.precedingInstructions.begin(),
                                                                   state.precedingInstructions.end());
            } else {
                LIGHT_PRINT("Context end\n");
            }
        }

        //Finds the functions that may be the entry points of threads
        //INPUT: The module to analyze and the set into which to insert
        //the results
        void findEntryPoints(Module &M, SmallPtrSet<Function*,4> &targetFunctions) {
            VERBOSE_PRINT("Determining entry points for threads...\n");
            //For each function that can spawn new threads, find the calls to that function
            for (StringRef funName : threadFunctions) {
                VERBOSE_PRINT("Finding functions used by " << funName << "\n");
                Function *fun = M.getFunction(funName);
                if (!fun) {
                    VERBOSE_PRINT("was not used by module\n");
                } else {
                    for (auto call = fun->users().begin(); call != fun->users().end(); ++call) {
                        //DEBUG_PRINT("Examining use: " << **call << "\n");
                        if (dyn_cast<Instruction>(*call) && isCallSite(dyn_cast<Instruction>(*call))) {
                            CallSite callsite(*call);
                            for (int opnum = 0; opnum < callsite.getNumArgOperands(); ++opnum) {
                                Value *funcOp = callsite.getArgOperand(opnum);
                                //DEBUG_PRINT("Examining argument: " << *funcOp << "\n");
                                //Try to resolve the value into a proper function
                                while (!isa<Function>(funcOp)) {
                                    if (isa<ConstantExpr>(funcOp)) {
                                        ConstantExpr *constOp = dyn_cast<ConstantExpr>(funcOp);
                                        if (constOp->isCast()) {
                                            funcOp = constOp->getAsInstruction();
                                            CastInst *castOp = dyn_cast<CastInst>(funcOp);
                                            Value* tempOp = funcOp;
                                            funcOp = castOp->getOperand(0);
                                            delete(tempOp);
                                        }
                                    } else if (isa<CastInst>(funcOp)) {
                                        CastInst *castOp = dyn_cast<CastInst>(funcOp);
                                        funcOp = castOp->getOperand(0);
                                    }
                                    else { //Unable To Resolve
                                        //DEBUG_PRINT("Failed to resolve argument " << *funcOp
                                        //<< " to a function, remaining type is:" << typeid(*funcOp).name() << "\n");
                                        break;
                                    }
                                }
                                if (auto spawnFunc = dyn_cast<Function>(funcOp)) {
                                    VERBOSE_PRINT("Targeting function: " << spawnFunc->getName() << "\n");
                                    targetFunctions.insert(spawnFunc);
                                }
                            }
                        }
                    }
                }
            }
        }

        //Utility: Determines whether a SynchronizationPoint should be
        //in an synchronizationVariable
        bool aliasWithSynchVar(SynchronizationPoint* synchPoint,SynchronizationVariable* synchVar) {
            SmallPtrSet<Value*,1> synchPoint1op;
            if (synchPoint->op != -1)
                synchPoint1op.insert(synchPoint->val->getOperand(synchPoint->op));
            else
                for (int i = 0; i < synchPoint->val->getNumOperands(); ++i)
                    synchPoint1op.insert(synchPoint->val->getOperand(i));
            for (SynchronizationPoint *synchPoint2 : synchVar->synchronizationPoints) {
                //if (pointerConflict(synchPoint->val,synchPoint2->val,wM))
                if (aacombined->MustConflict(synchPoint->val,synchPoint2->val))
                    return true;
                //for (Value* val : synchPoint1op) {
                
                // if (synchPoint2->op != -1) {
                //     if (alias(val,synchPoint2->val->getOperand(synchPoint2->op)))
                //         return true;
                // }
                // else
                //     for (int i = 0; i < synchPoint2->val->getNumOperands(); ++i)
                //         if (alias(val,synchPoint2->val->getOperand(i)))
                //             return true;
                //}
            }
            return false;
        }

        //Sets up the synchronizationVariables structure
        void determineSynchronizationVariables() {
            VERBOSE_PRINT("Determining synchronization variables...\n");
            for (SynchronizationPoint *synchPoint : synchronizationPoints) {
                VERBOSE_PRINT("Placing synchPoint " << synchPoint->ID << "\n");
                SmallPtrSet<SynchronizationVariable*,1> toDelete;
                for (auto it = synchronizationVariables.begin();
                     it != synchronizationVariables.end();) {
                    SynchronizationVariable *synchVar = *(it++);
                    if (aliasWithSynchVar(synchPoint,synchVar)) {
                        if (synchPoint->synchVar == NULL) {
                            VERBOSE_PRINT("Was placed into synchVar " << synchVar->ID << "\n");
                            synchPoint->setSynchronizationVariable(synchVar);
                        } else {
                            VERBOSE_PRINT("Merged other synchVar " << synchVar->ID
                                          << " into synchVar " << synchPoint->synchVar->ID << " due to multiple aliasing\n");
                            synchPoint->synchVar->merge(synchVar);
                            toDelete.insert(synchVar);
                            // synchronizationVariables.erase(synchVar);
                            // delete(synchVar);
                        }
                    }
                }
                for (SynchronizationVariable * synchVar : toDelete) {
                    synchronizationVariables.erase(synchVar);
                    delete(synchVar);
                }
                if (synchPoint->synchVar == NULL) {
                    SynchronizationVariable *newSynchVar = new SynchronizationVariable;
                    VERBOSE_PRINT("Was not placed into any synchVar, creating new synchVar with ID " << newSynchVar->ID << "\n");
                    synchPoint->setSynchronizationVariable(newSynchVar);
                    synchronizationVariables.insert(newSynchVar);
                }
            }            
        }

        //Sets up the criticalRegions structure
        void determineCriticalRegions(SmallPtrSet<Function*,4> entryPoints) {
            VERBOSE_PRINT("Determining critical regions...\n");
            //We know what the first synchpoints are in the entry functions, so we
            //start the analysis there
            for (Function *fun : entryPoints) {
                for (State funState : delimitFunctionDynamic[fun].leadingReverseStates) {
                    if (funState.lastSynch) {
                        sectionSynchronizationPointsIntoCriticalRegions(funState.lastSynch);
                        for (CriticalRegion * region : criticalRegions) {
                            if (region->containedSynchPoints.count(funState.lastSynch) != 0)
                                region->firstRegionInEntry=true;
                        }
                    }
                }
            }
        }

        //Meant to be called initially on one of the first synch points encountered in
        //a threads entry. Meaning it should be a synchpoint in a leadingReverseState
        //of an entrypoint function
        void sectionSynchronizationPointsIntoCriticalRegions(SynchronizationPoint* synchPoint) {
            //VERBOSE_PRINT("Starting Critical Region delimitation from synch point: " << synchPoint->ID << "\n");
            struct SearchState {
                SynchronizationPoint *nextPoint;
                int searchDepth;
                CriticalRegion *currRegion;
                SmallPtrSet<SynchronizationPoint*,1> acquiresSinceRegionStart;
                SmallPtrSet<SynchronizationPoint*,1> releasesSinceRegionStart;
            };
            deque<SearchState> workQueue;
            //The nesting levels we have handled this synch point at
            map<SynchronizationPoint*,set<int> > synchHandledNestLevels;
            SearchState newSearchState;
            newSearchState.nextPoint=synchPoint;
            newSearchState.searchDepth=0;
            newSearchState.currRegion=NULL;
            workQueue.push_back(newSearchState);
            while (!workQueue.empty()) {
                // DEBUG_PRINT("Queue contains: \n");
                // for (SearchState state : workQueue)
                //     DEBUG_PRINT("("<<state.nextPoint<<","<<state.searchDepth<<","<<state.currRegion<<")\n");
                // DEBUG_PRINT("\n");

                SearchState currState = workQueue.front();
                workQueue.pop_front();

                // if (currState.nextPoint)
                //     VERBOSE_PRINT("Handling synchpoint: " << currState.nextPoint->ID << "\n");
                // else
                //     VERBOSE_PRINT("Handling context end\n");
                // VERBOSE_PRINT("At depth: " << currState.searchDepth << "\n");
                // if (currState.currRegion)
                //     VERBOSE_PRINT("In region: " << currState.currRegion->ID << "\n");
                // else
                //     VERBOSE_PRINT("With no current region\n");

                if (currState.nextPoint == NULL) {
                    if (currState.searchDepth != 0) {
                        //VERBOSE_PRINT("Found end of graph context while nesting level was not zero\n");
                        //VERBOSE_PRINT("In region: " << currState.currRegion->ID << "\n");
                    }
                    continue;
                }

                //Todo: Detect cycles with ever-increasing nesting level
                //For example; a for-loop acquiring several locks

                //If we have already handled this synch point at this depth
                //skip it (most commonly skips handling it at depth 0)
                if (synchHandledNestLevels[currState.nextPoint].count(currState.searchDepth)) {
                    //VERBOSE_PRINT("Skipped due to already handled at thist nest level\n");
                    continue;
                }

                synchHandledNestLevels[currState.nextPoint].insert(currState.searchDepth);

                //When we are not in a critical section, we must create one
                //to handle synch points
                if (currState.searchDepth == 0) {
                    //If we encounter a synch point that does not start a critical region outside a critical region,
                    //stop that search branch as it cannot be an executable branch
                    if (!(currState.nextPoint->isCritBegin)) {
                        //VERBOSE_PRINT("Encountered synch point: " << currState.nextPoint->ID << "(value=" << *(currState.nextPoint->val) << ") while not in a critical region\n");
                        //VERBOSE_PRINT("Critical Region delimitation broken\n");
                        //return;
                        //assert("Encountered synch point not starting critical region outside critical region" && false);
                        continue;
                    }
                    
                    CriticalRegion *critRegion = currState.nextPoint->critRegion;
                    //If it's the first time we handled this synch point, create a new
                    //critical section for it
                    if (currState.nextPoint->critRegion == NULL) {
                        critRegion = new CriticalRegion;
                        currState.nextPoint->critRegion = critRegion;
                        criticalRegions.insert(critRegion);
                    }
                    //Add the current synchpoint to the entry points for
                    //this critical region
                    critRegion->containedSynchPoints.insert(currState.nextPoint);
                    critRegion->entrySynchPoints.insert(currState.nextPoint);
                    //Add the synch var used by the synch point to the synchsOn for
                    //the critical region
                    critRegion->synchsOn.insert(currState.nextPoint->synchVar);

                    SearchState newSearchState;
                    newSearchState.searchDepth=1;
                    newSearchState.currRegion=critRegion;
                    newSearchState.acquiresSinceRegionStart.insert(currState.nextPoint);
                    //Special case, point that both begins and ends a region
                    if (currState.nextPoint->isCritEnd) {
                        critRegion->exitSynchPoints.insert(currState.nextPoint);
                        newSearchState.currRegion=NULL;
                        newSearchState.searchDepth=0;
                        newSearchState.acquiresSinceRegionStart.clear();
                    }
                    for (SynchronizationPoint* synchPoint_ : currState.nextPoint->following) {
                        if (synchPoint_ != currState.nextPoint) {
                            newSearchState.nextPoint=synchPoint_;
                            workQueue.push_back(newSearchState);
                        } else {
                            //DEBUG_PRINT("Skipped searching through synchpoint " << synchPoint_->ID << " due to self-edge\n");
                        }
                    }
                } else {
                    //We are in a critical region, handle synchpoint accordingly
                    CriticalRegion* critRegion = currState.currRegion;
                    if (currState.nextPoint->critRegion != NULL) {
                        if (currState.nextPoint->critRegion != critRegion) {
                            critRegion->mergeWith(currState.nextPoint->critRegion);
                            criticalRegions.erase(critRegion);
                            //LIGHT_PRINT("Replacing " << critRegion->ID << " with " << currState.nextPoint->critRegion->ID << "\n");
                            // DEBUG_PRINT("Before:\n");
                            // for (SearchState state : workQueue) {
                            //     DEBUG_PRINT(state.currRegion << "\n");
                            // }
                            for (SearchState &state : workQueue) {
                                if (state.currRegion == critRegion)
                                    state.currRegion = currState.nextPoint->critRegion;
                            }
                            // DEBUG_PRINT("After:\n");
                            // for (SearchState state : workQueue) {
                            //     DEBUG_PRINT(state.currRegion << "\n");
                            // }
                            delete(critRegion);
                            critRegion=currState.nextPoint->critRegion;
                        }//  else {
                        //     //If we find a synchpoint again within the current
                        //     //region we have detected a loop. Stop search
                        //     //continue;
                        // }
                    } else {
                        currState.nextPoint->critRegion=critRegion;
                    }
                    int currDepth = currState.searchDepth;

                    SearchState newSearchState;
                    newSearchState.currRegion=critRegion;
                    newSearchState.acquiresSinceRegionStart=currState.acquiresSinceRegionStart;
                    newSearchState.releasesSinceRegionStart=currState.releasesSinceRegionStart;
                    //We might do some redundant work here, but it is fine
                    critRegion->containedSynchPoints.insert(currState.nextPoint);
                    //Add the synch var used by the synch point to the synchsOn for
                    //the critical region
                    critRegion->synchsOn.insert(currState.nextPoint->synchVar);
                    
                    //If this synch point begins a critical region, increase
                    //nesting level
                    if (currState.nextPoint->isCritBegin) {
                        if (currState.acquiresSinceRegionStart.count(currState.nextPoint) != 0)
                            continue;
                        else {
                            newSearchState.acquiresSinceRegionStart.insert(currState.nextPoint);
                            currDepth++;
                        }
                    }
                    //If this synch point ends a critical region, decrease
                    //nesting level
                    if (currState.nextPoint->isCritEnd) {
                        if (currState.releasesSinceRegionStart.count(currState.nextPoint) != 0)
                            //Loops back to itself will always mean it could terminate the region
                            currDepth=0;
                        else {
                            newSearchState.releasesSinceRegionStart.insert(currState.nextPoint);
                            currDepth--;
                        }
                        if (currDepth==0) {
                            if (critRegion->exitSynchPoints.count(currState.nextPoint) != 0) {             
                                //DEBUG_PRINT("Skipped searching through synchpoint " << synchPoint->ID << " due to it already ending a critical region\n");
                                continue;
                            }
                            //DEBUG_PRINT("Added synchpoint " << currState.nextPoint->ID << " as an endpoint to region " << critRegion->ID << "\n");
                            critRegion->exitSynchPoints.insert(currState.nextPoint);
                            newSearchState.currRegion=NULL;
                        }
                    }
                    newSearchState.searchDepth=currDepth;
                    for (SynchronizationPoint* synchPoint : currState.nextPoint->following) {
                        if (synchPoint != currState.nextPoint) {
                            newSearchState.nextPoint=synchPoint;
                            workQueue.push_back(newSearchState);
                        } else {
                            //DEBUG_PRINT("Skipped searching through synchpoint " << synchPoint->ID << " due to self-edge\n");
                        }
                    }
                }
            }
        }

        //The set of functions that may synchronize with other functions while executing
        SmallPtrSet<Function*,2> synchronizedFunctions;

        void determineSynchronizedFunctions() {
            deque<Value*> pthUsersQueue;
            SmallPtrSet<Value*,32> visitedValues;

            //for (auto pI = pthFunctions.begin(); pI != pthFunctions.end(); ++pI) {
            for (StringRef syncName : synchFunctions) {
                Function* syncFun = wM->getFunction(syncName);
                if (syncFun) {
                    for (auto uI = syncFun->users().begin(); uI != syncFun->users().end(); ++uI) {
                        pthUsersQueue.push_back(*uI);
                    }
                } else {
                    VERBOSE_PRINT("Module does not contain the synchronization function: " << syncName << "\n");
                }
            }
            
            while (!pthUsersQueue.empty()) {
                Value *nextVal = pthUsersQueue.front(); pthUsersQueue.pop_front();
                //If we have previously handled this value, skip it
                if (!(visitedValues.insert(nextVal).second))
                    continue;
                LIGHT_PRINT("Handling the value: " << nextVal->getName() << "\n");
                //Otherwise, if this value is an instruction, add the function it is
                //in to the synchronized functions. And add the users of that function
                //to the queue. If the function is previously handled then skip
                //adding the users of that function
                if (Instruction *user = dyn_cast<Instruction>(nextVal)) {
                LIGHT_PRINT("Was an instruction, adding parent: " << user->getParent()->getParent()->getName() << " as synchronized and adding the users of that function to the queue if it is not already handled\n");
                    
                    //If the instruction is a call, additionally track the called function
                    SmallPtrSet<Function*,1> calledFuns = getCalledFuns(user);
                    for (Function *cFun : calledFuns) {
                        LIGHT_PRINT(cFun->getName() << " is gonna be tracked probs\n");
                        pthUsersQueue.push_back(cFun);
                        // CallSite call(user);
                        // for (int i = 0; i < call.getNumArgOperands(); ++i) {
                        //     if (visitedValues.count(call.getArgOperand(i)) != 0) {
                        //         for (Argument &arg : cFun->getArgumentList()) {
                        //             if (arg.getArgNo() == i)
                        //                 pthUsersQueue.push_back(&arg);
                        //         }
                        //     }
                        // }
                    }
                    
                    Function *inFunction=user->getParent()->getParent();
                    if (!(synchronizedFunctions.insert(inFunction).second))
                        continue;
                    for (auto uI = inFunction->users().begin(); uI != inFunction->users().end(); ++uI) {
                        LIGHT_PRINT("Added " << uI->getName() << " as synchronized\n");
                        pthUsersQueue.push_back(*uI);
                    }                    
                } 
                //If the value is not an instruction, add the users of it to the queue
                else if (Function *fun = dyn_cast<Function>(nextVal)) {
                    LIGHT_PRINT("Was a function, adding it to synchronized functions\n");
                    synchronizedFunctions.insert(fun);
                } 
                else {
                    LIGHT_PRINT("Was not an instruction, adding users to queue\n");
                    for (auto uI = nextVal->users().begin(); uI != nextVal->users().end(); ++uI) {
                        pthUsersQueue.push_back(*uI);
                    }                    
                }
            }
        }

        map<Function*,SmallPtrSet<Instruction*,128> > getExecutableInstsDynamic;

        //Obtains all functions executable when executing fun
        SmallPtrSet<Instruction*,128> getExecutableInsts(Function *fun) {
            SmallPtrSet<Function*,4> visitedFuns;
            return getExecutableInstsDynamic[fun]=getExecutableInstsProper(fun,visitedFuns);
        }

        SmallPtrSet<Instruction*,128> getExecutableInstsProper(Function *fun, SmallPtrSet<Function*,4> &visitedFuns) {
            if (getExecutableInstsDynamic.count(fun) != 0)
                return getExecutableInstsDynamic[fun];

            SmallPtrSet<Instruction*,128> toReturn;
            if (visitedFuns.insert(fun).second) {
                for (inst_iterator it = inst_begin(fun);
                     it != inst_end(fun);
                     ++it) {
                    Instruction *inst = &*it;
                    if (isa<StoreInst>(inst) || isa<LoadInst>(inst))
                        toReturn.insert(inst);
                    SmallPtrSet<Function*,1> calledFuns = getCalledFuns(inst);
                    for (Function *cFun : calledFuns) {
                        SmallPtrSet<Instruction*,128> returned = getExecutableInstsProper(cFun,visitedFuns);
                        toReturn.insert(returned.begin(),returned.end());
                    }
                }
            }
            return toReturn;
        }
        
        //We color the synchronization points reachable from some synchronization point that creates threads
        //or reachable from a function first called by spawned threads
        SmallPtrSet<SynchronizationPoint*,32> coloredSynchs;
        void colorSynchPoints(SynchronizationPoint *start) {
            //Color the starting node
            if (coloredSynchs.insert(start).second == true) {
                //If we newly colored this node, recurse into successors
                if (start != NULL)
                    for (SynchronizationPoint * follower : start->following)
                        colorSynchPoints(follower);
            }
        }

        //Remove the preceding/following instructions towards synch points that are not colored
        void cleanSynchPoints() {
            for (SynchronizationPoint *synchPoint : synchronizationPoints) {
                for (SynchronizationPoint *pred : synchPoint->preceding) {
                    if (coloredSynchs.count(pred) == 0 || pred == NULL) {
                        synchPoint->precedingInsts[pred].clear();
                        // if (pred)
                        //     VERBOSE_PRINT("Cleaned instruction from synchpoint " << synchPoint->ID << " to synchpoint " << pred -> ID << "\n");
                        // else
                        //     VERBOSE_PRINT("Cleaned instruction from synchpoint " << synchPoint->ID << " to synchpoint context begin\n");
                    }
                }
                for (SynchronizationPoint *follow : synchPoint->following) {
                    if (coloredSynchs.count(follow) == 0) {
                        synchPoint->followingInsts[follow].clear();
                        // if (follow)
                        //     VERBOSE_PRINT("Cleaned instruction from synchpoint " << synchPoint->ID << " to synchpoint " << follow -> ID << "\n");
                        // else
                        //     VERBOSE_PRINT("Cleaned instruction from synchpoint " << synchPoint->ID << " to synchpoint context end\n");
                    }
                }
            }
        }
    };    
}

char SynchPointDelim::ID = 0;
//namespace llvm {
// INITIALIZE_PASS_BEGIN(SynchPointDelim, "SPDelim",
//                       "Identifies synchronization points and critical regions", true, true)
// INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
// INITIALIZE_PASS_END(SynchPointDelim, "SPDelim",
//                     "Identifies synchronization points and critical regions", true, true)
//}

static RegisterPass<SynchPointDelim> X("SPDelim",
                                       "Identify Synch Points and Data Conflicts pass",
                                       true,
                                       true);

#endif

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
