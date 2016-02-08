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
#define PRINT PRINTSTREAM << "SynchPointDelim: "
#define PRINT_DEBUG PRINTSTREAM << "SynchPointDelim (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

namespace {
    //These are the functions to treat as synchronization points
    set<StringRef> synchFunctions = {"pthread_mutex_lock",
                                     "pthread_mutex_unlock"};

    //These are the function to treat as if they spawn new
    //threads
    set<StringRef> threadFunctions = {"pthread_create"};

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

        //The main runOnModule function is divided in three parts
        //The first part finds synchronization points and the drf paths between
        //them
        //The second part determines which synchronization points synch with
        //eachother
        //The third part finds data conflicts across synchronizations points
        virtual bool runOnModule(Module &M) {
            //Functions that may be the entry point of functions
            SmallPtrSet<Function*,4> entrypoints;
            
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
            }

            //Determine what synchronization variables we have
            determineSynchronizationVariables();

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
                SmallPtrSet<SynchronizationPoint*, 1> firstReachable;
                vector<State> toReturn = delimitFromBlock(&(start->getEntryBlock()),states,&firstReachable);
                delimitFunctionDynamic[start]=make_pair(toReturn,firstReachable);
            }
            return delimitFunctionDynamic[start].first;
        }

        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states,
                                       SmallPtrSet<SynchronizationPoint*,1> *firstReachable) {
            return delimitFromBlock(curr,states,firstReachable,NULL);
        }        

        //Delimits synchronization points starting with the specified block
        //Input: Block to start at and The state before analyzing, as well
        //as the set to store the first encountered synch points in
        //(if null, they are not stored). Also takes the block this search
        //branched from, if any
        //Returns: A set of states, one for each end point of the search
        //Side-effects: Updates the synchronization point variables
        //with the paths discoverable from this basic block
        vector<State> delimitFromBlock(BasicBlock *curr,vector<State> states,
                                       SmallPtrSet<SynchronizationPoint*,1> *firstReachable,
                                       BasicBlock *prev) {
            DEBUG_PRINT("Started a new search branch from BasicBlock: "<< curr->getName() << "\n");

            //This is the set of states of sub-branches that we need to keep
            //track of. These will be returned together with the states
            //obtained in the current search once we return
            vector<State> finishedSearchStates;
            
            //This is the set of edges (basicblock to basicblock) that we should
            //ignore while branching. Basically we never want to follow the same
            //edge twice while analyzing.
            set<pair<BasicBlock*,BasicBlock*> > forbiddenEdges;
            if (prev)
                forbiddenEdges.insert(make_pair(prev,curr));

            while (curr) {
                //Analyze the current block
                for (BasicBlock::iterator currb=curr->begin(),
                         curre=curr->end();
                     currb != curre; ++currb) {
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
                        }
                        //Toss the synchpoint upwards if we should
                        if (firstReachable) {
                            //Only do this once, we only need to pass
                            //the first synchpoints we encounter
                            firstReachable->insert(synchPoint);
                            firstReachable=NULL;
                        }
                        //Perform updates
                        for (State &state : states) {
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
                            return vector<State>();
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
                                if (!calledFun->empty()) {
                                    //Parse the function and obtain the states
                                    //that are at the exit of the function
                                    DEBUG_PRINT("Analysing CG of " << calledFun->getName() << "\n");
                                    states = delimitFunction(calledFun,states);
                                    
                                    //This is kinda-sorta hacky, but if we have
                                    //not yet discovered any synch-points we can
                                    //take all of the first-encountered synchpoints
                                    //in the called function and say we can
                                    //encounter them first here, too
                                    if (firstReachable) {
                                        SmallPtrSet<SynchronizationPoint*,1> firstEnc = delimitFunctionDynamic[calledFun].second;
                                        if (!firstReachable->empty()) {
                                            firstReachable->insert(firstEnc.begin(),firstEnc.end());
                                            firstReachable=NULL;
                                        }
                                    }
                                } else {
                                    DEBUG_PRINT("Skipped analysis of " << calledFun->getName() << " due to it having no function body\n");
                                }
                                //Continue analysis as usual with those states
                            } else {
                                //We failed to determine which function could
                                //be called, print an error about this
                                VERBOSE_PRINT("Failed to determine the function called by: " << *currb << ", ignoring the error\n");
                            }
                        }
                        else {
                            //Otherwise, simply add the instruction to the
                            //states we're tracking
                            DEBUG_PRINT("Added " << *currb << " to:\n");
                            for (State &state : states) {
                                if (state.lastSynch)
                                    DEBUG_PRINT("ID " << state.lastSynch->ID << "\n");
                                else
                                    DEBUG_PRINT("Context start\n");
                                state.precedingInstructions.insert(currb);
                            }
                        }
                    }
                }
                //After we're done with the current block, handle successor
                //blocks. But frst we set up the ending iterator to point to
                //the block after the last block whose edge is not forbidden
                succ_iterator
                    bb = succ_begin(curr),
                    be = succ_begin(curr),
                    bbe = succ_end(curr);

                DEBUG_PRINT("Finding branches from " << curr->getName() << "\n");
                //Set be to be the last basicblock to which the edge is not
                //forbidden
                while (bb != bbe) {
                    if (forbiddenEdges.count(make_pair(curr,*bb)) == 0) {
                        be=bb++;
                    }
                }
                bb = succ_begin(curr);
                
                //Handle case where basicblock has no legal successors
                if (bb == be) {
                    DEBUG_PRINT("DFS path ended in BasicBlock: " << curr->getName() << " due to no viable branches\n");
                    curr = NULL;
                }
                //Handle successors, ignore successors that are forbidden to
                //branch on
                else {
                    DEBUG_PRINT("Last viable branch was: " << (*be)->getName() << "\n");
                    //Let current function call handle the last
                    //successor that can be branched on
                    while (bb != be) {
                        if (bb+1 == be) {
                            forbiddenEdges.insert(make_pair(curr,*bb));
                            curr=*bb;
                        }
                        else {
                            //Perform a new function call on the branch, obtaining
                            //the resulting state
                            //Remember if the branches need to track first reached
                            //synch points
                            if (forbiddenEdges.count(make_pair(curr,*bb)) == 0) {
                                vector<State> resultStates = delimitFromBlock(*bb,states,firstReachable,curr);
                                finishedSearchStates.insert(finishedSearchStates.end(),
                                                            resultStates.begin(),resultStates.end());
                            }
                        }
                        ++bb;
                    }
                }
            }
            finishedSearchStates.insert(finishedSearchStates.end(),
                                        states.begin(),states.end());
            return finishedSearchStates;
        }

        //Print information about synch points and synch variables
        void printInfo() {
            VERBOSE_PRINT("Printing synchronization point info...\n");
            //Print info about synch points
            for (SynchronizationPoint* synchPoint : synchronizationPoints) {
                VERBOSE_PRINT("Synch Point: " << synchPoint->ID << "\n");
                VERBOSE_PRINT("Value: " << *(synchPoint->val) << "\n");
                VERBOSE_PRINT("Preceding:\n");
                for (SynchronizationPoint* precedingPoint : synchPoint->preceding) {
                    if (precedingPoint) {
                        VERBOSE_PRINT("ID: " << precedingPoint->ID << "\n");
                    } else {
                        VERBOSE_PRINT("Context start\n");
                    }
                    for (auto it=synchPoint->precedingInsts[precedingPoint].begin(),
                             et=synchPoint->precedingInsts[precedingPoint].end();
                         it != et; ++it)
                        VERBOSE_PRINT(**it << "\n");
                }
                VERBOSE_PRINT("Following:\n");
                for (SynchronizationPoint* followingPoint : synchPoint->following) {
                    if (followingPoint) {
                        VERBOSE_PRINT("ID: " << followingPoint->ID << "\n");
                    } else {
                        VERBOSE_PRINT("Context end\n");
                    }
                    for (auto it=synchPoint->followingInsts[followingPoint].begin(),
                             et=synchPoint->followingInsts[followingPoint].end();
                         it != et; ++it)
                        VERBOSE_PRINT(**it << "\n");
                }
            }
            VERBOSE_PRINT("Printing synchronization variable info...\n");
            for (SynchronizationVariable *synchVar : synchronizationVariables) {
                VERBOSE_PRINT("Synch VAR: " << synchVar->ID << "\n");
                VERBOSE_PRINT("Contains: (ID|VALUE)\n");
                for (SynchronizationPoint *synchPoint : synchVar->synchronizationPoints) {
                    VERBOSE_PRINT(synchPoint->ID << " ; " << *(synchPoint->val) << "\n");
                }
                VERBOSE_PRINT("Data conflicts (FROM|TO):\n");
                for (pair<Instruction*,Instruction*> conflict : synchVar->conflicts) {
                    VERBOSE_PRINT(*(conflict.first) << " ; " << *(conflict.second) << "\n");
                }
            }            
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
            if (state.lastSynch != NULL) {
                DEBUG_PRINT("Updating following instructions of syncpoint " << state.lastSynch->ID << "\n");
                DEBUG_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                state.lastSynch->following.insert(synchPoint);
                state.lastSynch->followingInsts[synchPoint].insert(state.precedingInstructions.begin(),
                                                                   state.precedingInstructions.end());
            }
            if (synchPoint) {
                DEBUG_PRINT("Updating preceding instructions of syncpoint " << synchPoint->ID << "\n");
                DEBUG_PRINT("Tracked "<<state.precedingInstructions.size() << " instructions\n");
                synchPoint->preceding.insert(state.lastSynch);
                synchPoint->precedingInsts[state.lastSynch].insert(state.precedingInstructions.begin(),
                                                               state.precedingInstructions.end());
            }
        }

        //Finds the functions that may be the entry points of threads
        //INPUT: The module to analyze and the set into which to insert
        //the results
        void findEntryPoints(Module &M, SmallPtrSet<Function*,4> &targetFunctions) {
            //For each function that can spawn new threads, find the calls to that function
            for (StringRef funName : threadFunctions) {
                VERBOSE_PRINT("Finding functions used by " << funName << "\n");
                Function *fun = M.getFunction(funName);
                if (!fun) {
                    VERBOSE_PRINT("was not used by module\n");
                } else {
                    for (auto call = fun->users().begin(); call != fun->users().end(); ++call) {
                        DEBUG_PRINT("Examining use: " << **call << "\n");
                        if (CallInst *callsite = dyn_cast<CallInst>(*call)) {
                            for (int opnum = 0; opnum < callsite->getNumArgOperands(); ++opnum) {
                                Value *funcOp = callsite->getArgOperand(opnum);
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
            return false; //Dummy for now
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
                for (Value* val : synchPoint1op) {
                    if (synchPoint2->op != -1) {
                        if (alias(val,synchPoint2->val->getOperand(synchPoint2->op)))
                            return true;
                    }
                    else
                        for (int i = 0; i < synchPoint2->val->getNumOperands(); ++i)
                            if (alias(val,synchPoint2->val->getOperand(i)))
                                return true;
                }
            }
            return false;
        }

        //Sets up the synchronizationVariables structure
        void determineSynchronizationVariables() {
            DEBUG_PRINT("Determining synchronization variables...\n");
            for (SynchronizationPoint *synchPoint : synchronizationPoints) {
                DEBUG_PRINT("Placing synchPoint " << synchPoint->ID << "\n");
                for (SynchronizationVariable *synchVar : synchronizationVariables) {
                    if (aliasWithSynchVar(synchPoint,synchVar)) {
                        if (synchPoint->synchVar == NULL) {
                            DEBUG_PRINT("Was placed into synchVar " << synchVar->ID << "\n");
                            synchPoint->setSynchronizationVariable(synchVar);
                        } else {
                            DEBUG_PRINT("Merged other synchVar " << synchVar->ID
                                        << " into synchVar " << synchPoint->synchVar->ID << " due to multiple aliasing\n");
                            synchPoint->synchVar->merge(synchVar);
                            delete(synchVar);
                        }
                    }
                }
                if (synchPoint->synchVar == NULL) {
                    DEBUG_PRINT("Was not placed into any synchVar, creating new synchVar\n");
                    SynchronizationVariable *newSynchVar = new SynchronizationVariable;
                    synchPoint->setSynchronizationVariable(newSynchVar);
                    synchronizationVariables.insert(newSynchVar);
                }
            }            
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
