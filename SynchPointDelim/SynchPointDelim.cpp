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
// #include <queue>
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
// #include "llvm/IR/Constants.h"
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
// #include "llvm/IR/InstIterator.h"
// #include "llvm/IR/Constants.h"
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

#define LIBRARYNAME "SynchPointDelim"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT_VERBOSE PRINTSTREAM << "SynchPointDelim: "
#define PRINT_DEBUG PRINTSTREAM << "SynchPointDelim (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT_VERBOSE << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

namespace {
    //These are the functions to treat as synchronization points
    set<StringRef> synchFunctions = {};

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

        //The state tracks the DFS of the program flow
        //Contains the most recent synch point tracked on this path
        //Contains the instructions executable since passing that
        //synch point
        class State {
        public:
            SynchronizationPoint* lastSynch;
            SmallPtrSet<Instruction*,32> precedingInstructions;
        };

        //Top-level delimitation for a function, should commonly only be
        //called on main
        //Disregards synchronization until the point that a thread has been
        //created
        void topLevelDelimitForFunction(Function *functionStart) {
            
        }

        //This is a dynamic-programming style map from functions
        //to pairs of vector of states and sets of sync points that lets
        //us avoid analyzing the same function twice
        //The first part of the pair bound to each function is the resulting
        //states after analyzing it
        //The second part of the pair bound to each function is the
        //collection of synch points that need to have their preceding
        //sets updated according to the new calling context
        map<Function*,pair<vector<State>,
                           SmallPtrSet<SynchronizationPoint*, 1> >
            > delimitFunctionDynamic; 

        //Delimits synchronization points for a particular function
        //Input: Function to analyze and the states to track before analysing
        //Returns: A set of set of states, one state for each exit point
        //and each path to reach that exit point
        //Side-effects: Updates all the synchronization points within the
        //function correctly
        vector<State> delimitFunction(Function *start,vector<State> states) {
            DEBUG_PRINT("Starting analysis of function: " << start->getName() << "\n");
            //Check if we have handled this function previously
            if (delimitFunctionDynamic.count(start) != 0) {
                DEBUG_PRINT("Previously handled - dynamic resolution\n");
                //Update the synch points that are accessible from the
                //entry of the function such that their preceding paths
                //contain the current preceding paths
                for (SynchronizationPoint *point : delimitFunctionDynamic[start].second) {
                    for (State state : states) {
                        updateSynchPointWithState(state,point);
                    }
                }
            } else {
                //Start analysis of the function
                vector<State> toReturn = delimitFromBlock(&(start->getEntryBlock()),states);
                //TODO: Make delimitFromBlock return the first synch variables found
                //on each branch
                SmallPtrSet<SynchronizationPoint*, 1> dummy;
                delimitFunctionDynamic[start]=make_pair(toReturn,dummy);
            }
            return delimitFunctionDynamic[start].first;
        }

        //Delimits synchronization points starting with the specified block
        //Input: Block to start at and The state before analyzing
        //Returns: A set of states, one for each end point of the search
        //Side-effects: Updates the synchronization point variables
        //with the paths discoverable from this basic block
        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states) {
            //TODO: Handle loops that do not cotnain synch points
            //TODO: Return the first synch point encountered
            DEBUG_PRINT("Started a new search branch from BasicBlock: "<< curr << "\n");

            //This is the set of states of sub-branches that we need to keep
            //track of. These will be returned together with the states
            //obtained in the current search once we return
            vector<State> finishedSearchStates;

            while (curr) {
                //Analyze the current block
                for (BasicBlock::iterator currb=curr->begin(),
                         curre=curr->end();
                     currb != curre; ++currb) {
                    if (isSynch(currb)) {
                        //Handle synchronization point
                        //See if we've already visited this point
                        DEBUG_PRINT("Visited instruction that is synch point: " << currb << "\n");
                        SynchronizationPoint *synchPoint = findSynchPoint(synchronizationPoints,currb);
                        bool visited = true;
                        if (!synchPoint) {
                            visited = false;
                            DEBUG_PRINT("Was not previously visited\n");
                            //If not, create a new synchronization point
                            synchPoint = new SynchronizationPoint;
                            synchPoint->val=currb;
                        }
                        //Perform updates
                        for (State state : states) {
                            updateSynchPointWithState(state,synchPoint);
                        }
                        //Clear previous states, all searched paths end here
                        states.clear();
                        //If we're not the first one here, then someone else
                        //has already taken care of all the following
                        //paths and we need not continue
                        if (visited) {
                            //Return nothing, everything is already handled
                            //by previous searches
                            return vector<state>();
                        } else {
                            //Start a new path
                            State newState;
                            newState.lastSynch=synchPoint;
                            states.push_back(newState);
                        }
                    } else {
                        //If the instruction is a call, figure out which
                        //function it is
                        if (isa<CallInst>(currb)) {
                            //TODO: Handle function pointers and
                            //struct accesses
                            Function *calledFun = dyn_cast<CallInst>(currb)->getCalledFunction();
                            if (calledFun) {
                                //Parse the function and obtain the states
                                //that are at the exit of the function
                                DEBUG_PRINT("Analysing CG of " << calledFun->getName() << "\n");
                                states = delimitFunction(calledFun,states);
                                //Continue analysis as usual with those states
                            } else {
                                //We failed to determine which function could
                                //be called, print an error about this
                                VERBOSE_PRINT("Failed to determine the function called by: " << currb << ", ignoring the error\n");
                            }
                        }
                        else {
                            //Otherwise, simply add the instruction to the
                            //states we're tracking
                            for (State state : states)
                                state.precedingInstructions.insert(currb);
                        }
                    }
                }
                //After we're done with the current block, handle successor
                //blocks
                succ_iterator
                    bb = succ_begin(curr),
                    be = succ_end(curr);
                //Handle case where basicblock has no successors
                if (bb == be) {
                    DEBUG_PRINT("DFS path ended in BasicBlock: " << curr << "\n");
                    curr = NULL;
                }
                //Handle successors
                else {
                    //Let current function call handle the last
                    //successor
                    while (bb != be) {
                        if (bb+1 == be)
                            curr=*bb;
                        else {
                            //Perform a new function call on the branch, obtaining
                            //the resulting state
                            vector<State> resultStates = delimitFromBlock(*bb,states);
                            finishedSearchStates.insert(finishedSearchStates.end(),
                                                        resultStates.begin(),resultStates.end());
                        }
                        ++bb;
                    }
                }
            }
            finishedSearchStates.insert(finishedSearchStates.end(),
                                        states.begin(),states.end());
            return finishedSearchStates;
        }

        //Utility: Returns true if an instruction is a synchronization point
        bool isSynch(Instruction *inst) {
            //Simple heuristics: Only calls are synchronization points
            if (!isa<CallInst>(inst))
                return false;
            //Get the called function
            //TODO: Generalize to handle pointers and struct accesses
            Function *calledFun = dyn_cast<CallInst>(inst)->getCalledFunction();
            return calledFun && synchFunctions.count(calledFun->getName());
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

        //Utility: Given a synch point and a state, updates both as if the
        //state leads to the synch point
        void updateSynchPointWithState(State state,SynchronizationPoint *synchPoint) {
            state.lastSynch->following.insert(synchPoint);
            state.lastSynch->followingInsts[synchPoint].insert(state.precedingInstructions.begin(),
                                                               state.precedingInstructions.end());
            synchPoint->preceding.insert(state.lastSynch);
            synchPoint->precedingInsts[state.lastSynch].insert(state.precedingInstructions.begin(),
                                                               state.precedingInstructions.end());
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
