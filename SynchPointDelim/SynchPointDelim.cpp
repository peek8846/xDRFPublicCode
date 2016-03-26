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
#include "llvm/Analysis/CFG.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/TargetLibraryInfo.h"
// #include "llvm/Analysis/MemoryLocation.h"
// #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

// #include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"

#include "SynchPoint.hpp"
#include "UseChainAliasing.cpp"

#define LIBRARYNAME "SynchPointDelim"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "SynchPointDelim: "
#define PRINT_DEBUG PRINTSTREAM << "SynchPointDelim (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

namespace {
    //These are the functions that start critical regions:
    set<StringRef> critBeginFunctions = {"pthread_mutex_lock"};
    //These are the functions that end critical regions:
    set<StringRef> critEndFunctions = {"pthread_mutex_unlock"};
    //These are the functions that are 'from' in a one-way synchronization:
    set<StringRef> onewayFromFunctions = {"pthread_cond_signal",
                                          "pthread_cond_broadcast"};
    //These are the functions that are 'to' in a one-way synchronization:
    set<StringRef> onewayToFunctions = {"pthread_cond_wait"};

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
            synchFunctions.insert(critBeginFunctions.begin(),
                                  critBeginFunctions.end());
            synchFunctions.insert(critEndFunctions.begin(),
                                  critEndFunctions.end());
            synchFunctions.insert(onewayFromFunctions.begin(),
                                  onewayFromFunctions.end());
            synchFunctions.insert(onewayToFunctions.begin(),
                                  onewayToFunctions.end());
        }

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

        Module *wM;

        //The main runOnModule function is divided in three parts
        //The first part finds synchronization points and the drf paths between
        //them
        //The second part determines which synchronization points synch with
        //eachother
        //The third part finds data conflicts across synchronizations points
        virtual bool runOnModule(Module &M) {
            //Functions that may be the entry point of functions
            SmallPtrSet<Function*,4> entrypoints;

            wM=&M;
            
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
                State dummyState;
                dummyState.lastSynch=NULL;
                vector<State> startingDummyStates;
                startingDummyStates.push_back(dummyState);
                vector<State> endingPoints;
                endingPoints = delimitFunction(target,startingDummyStates);
                for (State state : endingPoints) {
                    updateSynchPointWithState(state,NULL);
                }
                for (pair<BasicBlock* const,SmallPtrSet<State*,2> > &bb : visitedBlocks) {
                    for (State* state : bb.second)
                        delete state;
                }
                visitedBlocks.clear();
            }

            //Determine what synchronization variables we have
            determineSynchronizationVariables();

            //Determine the critical regions we have
            determineCriticalRegions(entrypoints);

            //Determine the data-flow conflicts across these points
            //determineDataflowConflicts();

            //Print the info
            printInfo();
            
            return false; //Pure analysis, should not change any code
        }

        //These data structures are the results of the analysis
        //TODO: There should propably be interface functions towards
        //synchronization variables that mean that direct access
        //to synchronizationPoints are not necessary
        SmallPtrSet<SynchronizationPoint*,32> synchronizationPoints;
        SmallPtrSet<SynchronizationVariable*,8> synchronizationVariables;
        SmallPtrSet<CriticalRegion*,8> criticalRegions;

    private:

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
        vector<State> delimitFunction(Function *start,vector<State> states) {
            set<CallSite> noRecurseSet;
            return delimitFunction(start,states,noRecurseSet,CallSite());
        }

        vector<State> delimitFunction(Function *start,vector<State> states, set<CallSite> &noRecurseSet, CallSite callInst) {
            DEBUG_PRINT("Starting analysis of function: " << start->getName() << "\n");
            //Check if we have handled this function previously
            if (delimitFunctionDynamic.count(start) != 0 &&
                delimitFunctionDynamic[start].astate == FunctionAnalysisState::Analyzed) {
                DEBUG_PRINT("Previously handled - dynamic resolution\n");
            } else {
                if (delimitFunctionDynamic.count(start) != 0 && delimitFunctionDynamic[start].astate == FunctionAnalysisState::BeingAnalyzed) {
                    DEBUG_PRINT("Encountered recursion - added to no-recurse set\n");
                    if (isNotNull(callInst))
                        noRecurseSet.insert(callInst);
                }
                
                //Start analysis of the function
                FunctionAnalysisState funState;
                funState.astate = FunctionAnalysisState::BeingAnalyzed;
                delimitFunctionDynamic[start]=funState;
                State dummyState;
                dummyState.lastSynch = NULL;
                vector<State> dummyVector;
                dummyVector.push_back(dummyState);
                vector<State> trailStates = delimitFromBlock(&(start->getEntryBlock()),dummyVector,
                                                             &(delimitFunctionDynamic[start].leadingReverseStates),
                                                             noRecurseSet);
                delimitFunctionDynamic[start].astate = FunctionAnalysisState::Analyzed;
                delimitFunctionDynamic[start].trailingStates.insert(delimitFunctionDynamic[start].trailingStates.begin(),
                                                                    trailStates.begin(),
                                                                    trailStates.end());
            }

            vector<State> toReturn;
            //Update the synch points that are accessible from the
            //entry of the function such that their preceding paths
            //contain the current preceding paths
            DEBUG_PRINT("Function analysis of "<< start->getName()<< " done, updating states and synch points\n");
            DEBUG_PRINT("Cross size is: " << delimitFunctionDynamic[start].leadingReverseStates.size() << "x"
                        << states.size() << "\n");
            for (State leadState : delimitFunctionDynamic[start].leadingReverseStates) {
                for (State state : states) {
                    state.precedingInstructions.insert(leadState.precedingInstructions.begin(),
                                                       leadState.precedingInstructions.end());
                    updateSynchPointWithState(state,leadState.lastSynch);
                }
            }
            DEBUG_PRINT("Updates done, setup return:\n");
            DEBUG_PRINT("Cross size is: " << delimitFunctionDynamic[start].trailingStates.size() << "x("
                                                << states.size() << ")\n");
            
            //Return the states that trail from the function
            for (State trailState : delimitFunctionDynamic[start].trailingStates) {
                if (trailState.lastSynch != NULL)
                    toReturn.push_back(trailState);
                else {
                    //Edge case, there is no synch point on this path through the
                    //function, we need to add the instructions encountered
                    //to the preceding states
                    //and return accordingly
                    for (State state : states) {
                        state.precedingInstructions.insert(trailState.precedingInstructions.begin(),
                                                           trailState.precedingInstructions.end());
                        toReturn.push_back(state);
                    }
                }
            }
            if (isNotNull(callInst))
                DEBUG_PRINT("Handled function call: " << *(callInst.getInstruction()) << "\n");

            return toReturn;
        }

        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states,
                                       vector<State> *firstReachable,
                                       set<CallSite> &noRecurseSet) {
            //map<BasicBlock*,SmallPtrSet<SynchronizationPoint*,2> > dummy;
            SmallPtrSet<Instruction*,64> dummy2;
            return delimitFromBlock(curr,states,firstReachable,noRecurseSet,
                                    SmallPtrSet<BasicBlock*,64>(),
                                    dummy2);
        }

        //Brute force dbeug chekc
        //SmallPtrSet<Instruction*,128> allHandledInsts;

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
                                       vector<State> *firstReachable,
                                       set<CallSite> &noRecurseSet,
                                       SmallPtrSet<BasicBlock*,64> previousBlocks,
                                       SmallPtrSet<Instruction*,64> &backAddedInsts) {
            DEBUG_PRINT("Started a new search branch from BasicBlock: "<< curr->getName() << "\n");

            states=unifyRedundantStates(states);

            SmallPtrSet<Instruction*,64> backAddedInstsLocal;

            //This is the set of states of sub-branches that we need to keep
            //track of. These will be returned together with the states
            //obtained in the current search once we return
            vector<State> finishedSearchStates;
            
            while (curr) {
                DEBUG_PRINT("Handling BasicBlock: " << curr->getName() << "\n");
                DEBUG_PRINT("Previously finished basicblocks are:\n");
                for (pair<BasicBlock* const,SmallPtrSet<State*,2> > &bb : visitedBlocks)
                    DEBUG_PRINT("  " << bb.first->getName() << "\n");
                DEBUG_PRINT("Previously visited blocks on this branch are:\n");
                for (BasicBlock* bb : previousBlocks)
                    DEBUG_PRINT("  " << bb->getName() << "\n");
                DEBUG_PRINT("Most recently visited synch points are:\n");
                for (State state : states)
                    if (state.lastSynch)
                        DEBUG_PRINT("  " << state.lastSynch->ID << "\n");
                    else
                        DEBUG_PRINT("  context begin\n");

                //Backedge case
                if (previousBlocks.count(curr) != 0) {
                    DEBUG_PRINT("Search stopped in block: " << curr->getName() << " due to backedge\n");
                    for (State state : states) {
                        backAddedInsts.insert(state.precedingInstructions.begin(),
                                              state.precedingInstructions.end());
                    }
                    //Should not need to return anything extra
                    curr=NULL;
                    continue;
                }
                //Forward-edge case || Back-edge case across synch points
                else if (visitedBlocks.count(curr) != 0) {
                    DEBUG_PRINT("Search stopped in block: " << curr->getName() << " due to forwardedge\n");
                    //We know this path must be completed, thus we simply check
                    //the mapping and find the reverse states from here
                    for (State state_ : states) {
                        speccCaseBackedgeBlocks[curr].push_back(state_);
                        for (State *state : visitedBlocks[curr]) {
                            state_.precedingInstructions.insert(state->precedingInstructions.begin(),
                                                                state->precedingInstructions.end());
                            updateSynchPointWithState(state_,state->lastSynch);
                            //If the state reaches context end, return it
                            if (state->lastSynch == NULL) {
                                finishedSearchStates.push_back(state_);
                            }
                        }
                        speccCaseBackedgeBlocks[curr]=unifyRedundantStates(speccCaseBackedgeBlocks[curr]);
                    }
                    curr=NULL;
                    continue;
                }

                previousBlocks.insert(curr);

                //Analyze the current block
                for (BasicBlock::iterator currb=curr->begin(),
                         curre=curr->end();
                     currb != curre; ++currb) {
                    // if (!(allHandledInsts.insert(&*currb).second)) {
                    //     // DEBUG_PRINT("Instruction was: " << *currb << "\nin basic block: " << curr->getName() << "\n");
                    //     assert("Handled the same instruction twice!");
                    // }
                    
                    if (isSynch(currb)) {
                        //Handle synchronization point
                        //See if we've already visited this point
                        DEBUG_PRINT("Visited instruction that is synch point: " << *currb << "\n");
                        SynchronizationPoint *synchPoint = findSynchPoint(synchronizationPoints,currb);
                        bool visited = true;
                        if (!synchPoint) {
                            visited = false;
                            DEBUG_PRINT("Was not previously visited\n");
                            //If not, create a new synchronization point
                            synchPoint = new SynchronizationPoint;
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
                        if (firstReachable) {
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
                            firstReachable->push_back(newState);
                            firstReachable=NULL;
                        }
                        //Perform updates
                        for (State &state : states) {
                            updateSynchPointWithState(state,synchPoint);
                        }

                        //Update previous basicblocks to shortcut searches through them
                        for (BasicBlock* block : previousBlocks) {
                            DEBUG_PRINT("Added BB " << block->getName() << " having the follower Synchpoint " << synchPoint->ID << "\n");
                            for (State state : states) {
                                State* newState = new State;
                                newState->lastSynch=synchPoint;
                                newState->precedingInstructions=state.precedingInstructions;
                                visitedBlocks[block].insert(newState);
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
                            previousBlocks.clear();
                            // //Don't want to clear previousVisited, so instead
                            // //create a new one
                            // map<BasicBlock*,SmallPtrSet<SynchronizationPoint*,2> > visitedBlocks_;
                            // visitedBlocks=visitedBlocks_;
                        }
                    } else {
                        //If the instruction is a call, figure out which
                        //function it is
                        if (isCallSite(currb)) {
                            SmallPtrSet<Function*,1> calledFuns = getCalledFuns(currb);
                            for (Function* calledFun : calledFuns) {
                                //Don't recurse on this function call
                                if (noRecurseSet.count(CallSite(currb)) != 0) {
                                    DEBUG_PRINT("DFS path ended in BasicBlock: " << curr->getName() << " due to already processed recursive call\n");
                                    curr = NULL;
                                    continue;
                                } else if (!calledFun->empty()) {
                                    //Parse the function and obtain the states
                                    //that are at the exit of the function
                                    DEBUG_PRINT("Analysing CG of " << calledFun->getName() << "\n");
                                    states = delimitFunction(calledFun,states,noRecurseSet,CallSite(currb));
                                    
                                    //This is kinda-sorta hacky, but if we have
                                    //not yet discovered any synch-points we can
                                    //take all of the first-encountered synchpoints
                                    //in the called function and say we can
                                    //encounter them first here, too
                                    if (firstReachable) {
                                        vector<State> leadingStates = delimitFunctionDynamic[calledFun].leadingReverseStates;
                                        bool callHadSync = false;
                                        
                                        for (State state : leadingStates) {
                                            if (state.lastSynch != NULL) {
                                                callHadSync = true;
                                                for (State predState : states) {
                                                    state.precedingInstructions.insert(predState.precedingInstructions.begin(),
                                                                                       predState.precedingInstructions.end());
                                                }
                                            }
                                            firstReachable->push_back(state);
                                        }
                                        if (callHadSync)
                                            firstReachable = NULL;
                                    }
                                } else {
                                    DEBUG_PRINT("Added " << calledFun->getName() << " as an analyzed instruction due to it having no function body\n");
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
                            for (State &state : states) {
                                state.precedingInstructions.insert(currb);
                            }
                        }
                    }
                }
                succ_iterator
                    bb = succ_begin(curr),
                    bbe = succ_end(curr);
                
                if (curr->getSingleSuccessor())
                    curr = curr->getSingleSuccessor();
                else {
                    if (bb == bbe) {
                        DEBUG_PRINT("Search ended in " << curr->getName() << " due to no successing blocks\n");
                        //Update previous basicblocks to shortcut searches through them
                        for (BasicBlock* block : previousBlocks) {
                            DEBUG_PRINT("Added BB " << block->getName() << " being followed by context end\n");
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
                    } else 
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
                            DEBUG_PRINT("Branching from BB: " << curr->getName() << "\n");
                            vector<State> resultStates = delimitFromBlock(*bb,states,firstReachable,noRecurseSet,previousBlocks,backAddedInstsLocal);
                            //All instructions we got back must be added as preceding to all our current
                            //states, and also our parents
                            backAddedInsts.insert(backAddedInstsLocal.begin(),
                                                  backAddedInstsLocal.end());
                            for (State &state : states) {
                                state.precedingInstructions.insert(backAddedInstsLocal.begin(),
                                                                   backAddedInstsLocal.end());
                            }
                            finishedSearchStates.insert(finishedSearchStates.end(),
                                                        resultStates.begin(),resultStates.end());
                            
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
                        VERBOSE_PRINT("ID: " << precedingPoint->ID << "\n");
                    } else {
                        VERBOSE_PRINT("Context start\n");
                    }
                    // for (auto it=synchPoint->precedingInsts[precedingPoint].begin(),
                    //          et=synchPoint->precedingInsts[precedingPoint].end();
                    //      it != et; ++it)
                    //     VERBOSE_PRINT(**it << "\n");
                }
                VERBOSE_PRINT("Following:\n");
                for (SynchronizationPoint* followingPoint : synchPoint->following) {
                    if (followingPoint) {
                        VERBOSE_PRINT("ID: " << followingPoint->ID << "\n");
                    } else {
                        VERBOSE_PRINT("Context end\n");
                    }
                    // for (auto it=synchPoint->followingInsts[followingPoint].begin(),
                    //          et=synchPoint->followingInsts[followingPoint].end();
                    //      it != et; ++it)
                    //     VERBOSE_PRINT(**it << "\n");
                }
            }
            VERBOSE_PRINT("Printing synchronization variable info...\n");
            for (SynchronizationVariable *synchVar : synchronizationVariables) {
                VERBOSE_PRINT("Synch var: " << synchVar->ID << "\n");
                VERBOSE_PRINT("Contains: (ID|VALUE)\n");
                for (SynchronizationPoint *synchPoint : synchVar->synchronizationPoints) {
                    VERBOSE_PRINT(synchPoint->ID << " ; " << *(synchPoint->val) << "\n");
                }
                // VERBOSE_PRINT("Data conflicts (FROM|TO):\n");
                // for (pair<Instruction*,Instruction*> conflict : synchVar->conflicts) {
                //     VERBOSE_PRINT(*(conflict.first) << " ; " << *(conflict.second) << "\n");
                // }
            }
            VERBOSE_PRINT("Printng critical region info...\n");
            for (CriticalRegion *critRegion : criticalRegions) {
                VERBOSE_PRINT("Region: " << critRegion->ID << "\n");
                VERBOSE_PRINT("Synchronizes on:\n");
                for (SynchronizationVariable* synchVar : critRegion->synchsOn) {
                    VERBOSE_PRINT("Synch Var: " << synchVar->ID << "\n");
                }
                VERBOSE_PRINT("Entry points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->entrySynchPoints) {
                    VERBOSE_PRINT("Synch Point: " << synchPoint->ID << "\n");
                }
                VERBOSE_PRINT("Contains points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->containedSynchPoints) {
                    VERBOSE_PRINT("Synch Point: " << synchPoint->ID << "\n");
                }
                VERBOSE_PRINT("Exit points:\n");
                for (SynchronizationPoint* synchPoint : critRegion->exitSynchPoints) {
                    VERBOSE_PRINT("Synch Point: " << synchPoint->ID << "\n");
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
            //DEBUG_PRINT("Finding functions that can be called by " << *inst << "\n");
            SmallPtrSet<Function*,1> toReturn;
            SmallPtrSet<Value*,8> alreadyVisited;
            if (isCallSite(inst)) {
                //DEBUG_PRINT("which is a callsite\n");
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
                    if (auto fun = dyn_cast<Function>(nextValue))
                        toReturn.insert(fun);
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
                        //at this point we can basically give up, any function
                        //that has its adress taken can be used here
                        for (Function &fun : inst->getParent()->getParent()->getParent()->getFunctionList()) {
                            if (fun.hasAddressTaken())
                                toReturn.insert(&fun);
                        }
                    }
                    else if (auto glob = dyn_cast<GlobalVariable>(nextValue)) {
                        //at this point we can basically give up, any function
                        //that has its adress taken can be used here
                        for (Function &fun : inst->getParent()->getParent()->getParent()->getFunctionList()) {
                            if (fun.hasAddressTaken())
                                toReturn.insert(&fun);
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
            // DEBUG_PRINT("Removing redundant states...\n");
            // DEBUG_PRINT("Removed " << (toMerge.size() - result.size()) << " states\n");
            return result;
        }

        //Utility: Given a synch point and a state, updates both as if the
        //state leads to the synch point
        void updateSynchPointWithState(State state,SynchronizationPoint *synchPoint) {
            DEBUG_PRINT("Started an update:\n");
            DEBUG_PRINT("Preceding: ");
            if (state.lastSynch != NULL) {
                DEBUG_PRINT("Synchpoint " << state.lastSynch->ID << "\n");
                //DEBUG_PRINT("Updating following instructions of syncpoint " << state.lastSynch->ID << "\n");
                //DEBUG_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                state.lastSynch->following.insert(synchPoint);
                state.lastSynch->followingInsts[synchPoint].insert(state.precedingInstructions.begin(),
                                                                   state.precedingInstructions.end());
            } else {
                DEBUG_PRINT("Context begin\n");
            }
            DEBUG_PRINT("Following: ");
            if (synchPoint) {
                DEBUG_PRINT("Synchpoint " << synchPoint->ID << "\n");
                //DEBUG_PRINT("Updating preceding instructions of syncpoint " << synchPoint->ID << "\n");
                //DEBUG_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                synchPoint->preceding.insert(state.lastSynch);
                synchPoint->precedingInsts[state.lastSynch].insert(state.precedingInstructions.begin(),
                                                               state.precedingInstructions.end());
            } else {
                DEBUG_PRINT("Context end\n");
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
                        DEBUG_PRINT("Examining use: " << **call << "\n");
                        if (dyn_cast<Instruction>(*call) && isCallSite(dyn_cast<Instruction>(*call))) {
                            CallSite callsite(*call);
                            for (int opnum = 0; opnum < callsite.getNumArgOperands(); ++opnum) {
                                Value *funcOp = callsite.getArgOperand(opnum);
                                DEBUG_PRINT("Examining argument: " << *funcOp << "\n");
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
                                        DEBUG_PRINT("Failed to resolve argument " << *funcOp
                                                    << " to a function, remaining type is:" << typeid(*funcOp).name() << "\n");
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

        //Determine whether two values refer to the same memory location
        bool alias(Value *val1, Value* val2) {
            return false;
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
                if (pointerConflict(synchPoint->val,synchPoint2->val,wM))
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
                    if (funState.lastSynch)
                        sectionSynchronizationPointsIntoCriticalRegions(funState.lastSynch);
                }
            }
        }

        //Meant to be called initially on one of the first synch points encountered in
        //a threads entry. Meaning it should be a synchpoint in a leadingReverseState
        //of an entrypoint function
        void sectionSynchronizationPointsIntoCriticalRegions(SynchronizationPoint* synchPoint) {
            DEBUG_PRINT("Starting Critical Region delimitation from synch point: " << synchPoint->ID << "\n");
            struct SearchState {
                SynchronizationPoint *nextPoint;
                int searchDepth;
                CriticalRegion *currRegion;
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

                if (currState.nextPoint)
                    DEBUG_PRINT("Handling synchpoint: " << currState.nextPoint->ID << "\n");
                else
                    DEBUG_PRINT("Handling context end\n");
                DEBUG_PRINT("At depth: " << currState.searchDepth << "\n");
                if (currState.currRegion)
                    DEBUG_PRINT("In region: " << currState.currRegion->ID << "\n");
                else
                    DEBUG_PRINT("With no current region\n");

                if (currState.nextPoint == NULL) {
                    if (currState.searchDepth != 0) {
                        VERBOSE_PRINT("Found end of graph context while nesting level was not zero\n");
                        VERBOSE_PRINT("In region: " << currState.currRegion->ID << "\n");
                    }
                    continue;
                }

                //Todo: Detect cycles with ever-increasing nesting level
                //For example; a for-loop acquiring several locks

                //If we have already handled this synch point at this depth
                //skip it (most commonly skips handling it at depth 0)
                if (synchHandledNestLevels[currState.nextPoint].count(currState.searchDepth))
                    continue;

                synchHandledNestLevels[currState.nextPoint].insert(currState.searchDepth);

                //When we are not in a critical section, we must create one
                //to handle synch points
                if (currState.searchDepth == 0) {
                    //The first encountered synch point must be the start of a critical section
                    assert("Encountered synch point not starting critical region outside critical region" &&
                           currState.nextPoint->isCritBegin);
                    
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
                    for (SynchronizationPoint* synchPoint : currState.nextPoint->following) {
                        if (synchPoint != currState.nextPoint) {
                            newSearchState.nextPoint=synchPoint;
                            workQueue.push_back(newSearchState);
                        }
                    }
                } else {
                    //We are in a critical region, handle synchpoint accordingly
                    CriticalRegion* critRegion = currState.currRegion;
                    if (currState.nextPoint->critRegion != NULL) {
                        if (currState.nextPoint->critRegion != critRegion) {
                            critRegion->mergeWith(currState.nextPoint->critRegion);
                            criticalRegions.erase(critRegion);
                            // DEBUG_PRINT("Replacing " << critRegion << "\n");
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
                        } else {
                            //If we find a synchpoint again within the current
                            //region we have detected a loop. Stop search
                            continue;
                        }
                    } else {
                        currState.nextPoint->critRegion=critRegion;
                    }
                    int currDepth = currState.searchDepth;

                    SearchState newSearchState;
                    newSearchState.currRegion=critRegion;
                    //We might do some redundant work here, but it is fine
                    critRegion->containedSynchPoints.insert(currState.nextPoint);
                    //Add the synch var used by the synch point to the synchsOn for
                    //the critical region
                    critRegion->synchsOn.insert(currState.nextPoint->synchVar);
                    
                    //If this synch point begins a critica region, increase
                    //nesting level
                    if (currState.nextPoint->isCritBegin) {
                        currDepth++;
                    }
                    //If this synch point ends a critical region, decrease
                    //nesting level
                    if (currState.nextPoint->isCritEnd) {
                        currDepth--;
                        if (currDepth==0) {
                            if (critRegion->exitSynchPoints.count(currState.nextPoint) != 0)
                                continue;
                            critRegion->exitSynchPoints.insert(currState.nextPoint);
                            newSearchState.currRegion=NULL;
                        }
                    }
                    newSearchState.searchDepth=currDepth;
                    for (SynchronizationPoint* synchPoint : currState.nextPoint->following) {
                        if (synchPoint != currState.nextPoint) {
                            newSearchState.nextPoint=synchPoint;
                            workQueue.push_back(newSearchState);
                        }
                    }
                }
            }
        }
        
        //Find the data flow conflicts across synchronization points
        // void determineDataflowConflicts() {
        //     for (SynchronizationVariable* synchVar : synchronizationVariables) {
        //         SmallPtrSet<Instruction*,128> preceding;
        //         SmallPtrSet<Instruction*,128> following;
        //         for (SynchronizationPoint* synchPoint : synchVar->synchronizationPoints) {
        //             SmallPtrSet<Instruction*,128> preceding_ = synchPoint->getPrecedingInsts();
        //             SmallPtrSet<Instruction*,128> following_ = synchPoint->getFollowingInsts();
        //             preceding.insert(preceding_.begin(),preceding_.end());
        //             following.insert(following_.begin(),following_.end());
        //         }
        //         for (Instruction* inst1 : preceding) {
        //             //Ignore anything that isn't a load or store
        //             //Might not want to ignore lib function calls
        //             if (!isa<StoreInst>(inst1) &&
        //                 !isa<LoadInst>(inst1))
        //                 continue;
        //             for (Instruction* inst2 : following) {
        //                 if (!isa<StoreInst>(inst2) &&
        //                     !isa<LoadInst>(inst2))
        //                     continue;
        //                 if (pointerConflict(inst1,inst2,wM))
        //                     synchVar->conflicts.insert(make_pair(inst1,inst2));
        //             }
        //         }
        //     }
        //}
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
