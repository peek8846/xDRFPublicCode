//===-------------------- Marks nDRF and xDRF regions ---------------------===//
// Marks the source code with the beginning and end of RMS regions
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

#define LIBRARYNAME "MarkRMSRegions"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "MarkRMSRegions: "
#define PRINT_DEBUG PRINTSTREAM << "MarkRMSRegions (debug): "

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

    set<StringRef> threadFunctions = {"pthread_create"};
    
    struct MarkRMSRegions : public ModulePass {
        static char ID;
        MarkRMSRegions() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
        }
      
        virtual bool runOnModule(Module &M) {

            VERBOSE_PRINT("Marking RMS calls in " << M.getName() << "\n");

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

            
	    beginNDRF = createDummyFunction("begin_NDRF",M);
	    endNDRF = createDummyFunction("end_NDRF",M);
	    beginXDRF = createDummyFunction("begin_XDRF",M);
	    endXDRF = createDummyFunction("end_XDRF",M);
            
            markInitialAcq(M);
            markInitialBarrier(M);
            markInitialAtomicAcq(M);
            markInitialAtomicRelease(M);
            markInitialAtomicAcqRel(M);
            markInitialSemWait(M);
            markInitialSemSignal(M);
            markParsecBarrier(M);
            
            for (Function * fun : entrypoints) {
                VERBOSE_PRINT("Marking entry/exit xDRF regions in " << fun->getName() << "\n");
                createDummyCall(beginXDRF,&*inst_begin(fun),true,TRACE_NUMBER);
                for (auto bit = inst_begin(fun),
                         bet = inst_end(fun);
                     bit != bet; ++bit) {
                    if (isa<ReturnInst>(&*bit))
                        createDummyCall(endXDRF,&*bit,TRACE_NUMBER);
                }
            }
            
            return true;
        }
    private:

        Function *beginNDRF;
        Function *endNDRF;
        Function *beginXDRF;
        Function *endXDRF;

        void markNextFinalRelease(Module &M,Instruction *start,bool enclave,SmallPtrSet<BasicBlock*,1>& visited_acqrelease) {
            Function * RMS_Final_Release = M.getFunction("RMS_Final_Release");
            assert(RMS_Final_Release && "Module contains RMS_Initial_Acq but not RMS_Final_Release");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_acqrelease.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>(&*inst)) {
                    if (call->getCalledValue()->stripPointerCasts() == RMS_Final_Release) {
                        //Mark it and return
                        if (!enclave)
                            createDummyCall(beginXDRF,call,false,0);
                        createDummyCall(endNDRF,call,false,0);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial acq not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Acq not followed by RMS_Final_Release @" << parent->getName() << "\n");
            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalRelease(M,&*(succ->begin()),enclave,visited_acqrelease);
        }

        void markInitialAcq(Module &M) {
            Function * RMS_Initial_Acq = M.getFunction("RMS_Initial_Acq");
            if (!RMS_Initial_Acq) {
                VERBOSE_PRINT("No regular locks to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_Acq->users()) {
                bool enclave;
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Find whether it is enclave
                    enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(1).get())->getZExtValue() == MOXDRF;
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalRelease(M,call,enclave,temp);
                }
            }
        }

        void markNextFinalBarrier(Module &M,Instruction *start,SmallPtrSet<BasicBlock*,1>& visited_barrier) {
            Function * RMS_Final_Barrier = M.getFunction("RMS_Final_Barrier");
            assert(RMS_Final_Barrier && "Module contains RMS_Initial_Barrier but not RMS_Final_Barrier");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_barrier.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_Barrier) {
                        //Mark it and return
                        createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial acq not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Barrier not followed by RMS_Final_Barrier @" << parent->getName() << "\n");
            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalBarrier(M,&*(succ->begin()),visited_barrier);
        }

        void markInitialBarrier(Module &M) {
            Function * RMS_Initial_Barrier = M.getFunction("RMS_Initial_Barrier");
            if (!RMS_Initial_Barrier) {
                VERBOSE_PRINT("No barriers to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_Barrier->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Mark it
                    createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalBarrier(M,call,temp);
                }
            }
        }

        void markNextFinalAtomicAcq(Module &M,Instruction *start,bool enclave, SmallPtrSet<BasicBlock*,1>& visited_atomic_acq) {
            Function * RMS_Final_Atomic_Acq = M.getFunction("RMS_Final_Atomic_Acq");
            assert(RMS_Final_Atomic_Acq && "Module contains RMS_Initial_Atomic_Acq but not RMS_Final_Atomic_Acq");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_acq.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_Atomic_Acq) {
                        //Mark it and return
                        if (!enclave)
                            createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial acq not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Atomic_Acq not followed by RMS_Final_Atomic_Acq @" << parent->getName() << "\n");
            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalAtomicAcq(M,&*(succ->begin()),enclave,visited_atomic_acq);
        }

        void markInitialAtomicAcq(Module &M) {
            Function * RMS_Initial_Atomic_Acq = M.getFunction("RMS_Initial_Atomic_Acq");
            if (!RMS_Initial_Atomic_Acq) {
                VERBOSE_PRINT("No atomic_acqs to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_Atomic_Acq->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Find whether it is enclave
                    bool enclave;
                    if (call->getNumArgOperands() > 2)
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MOXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalAtomicAcq(M,call,enclave,temp);
                }
            }
        }

        void markNextFinalAtomicRelease(Module &M,Instruction *start,bool enclave, SmallPtrSet<BasicBlock*,1>& visited_atomic_release) {
            Function * RMS_Final_Atomic_Release = M.getFunction("RMS_Final_Atomic_Release");
            assert(RMS_Final_Atomic_Release && "Module contains RMS_Initial_Atomic_Release but not RMS_Final_Atomic_Release");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_release.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_Atomic_Release) {
                        //Mark it and return
                        if (!enclave)
                            createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial release not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Atomic_Release not followed by RMS_Final_Atomic_Release @" << parent->getName() << "\n");

            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalAtomicRelease(M,&*(succ->begin()),enclave,visited_atomic_release);
        }

        void markInitialAtomicRelease(Module &M) {
            Function * RMS_Initial_Atomic_Release = M.getFunction("RMS_Initial_Atomic_Release");
            if (!RMS_Initial_Atomic_Release) {
                VERBOSE_PRINT("No atomic_releases to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_Atomic_Release->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Find whether it is enclave
                    bool enclave;
                    if (call->getNumArgOperands() > 2)
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MOXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalAtomicRelease(M,call,enclave,temp);
                }
            }
        }

        void markNextFinalAtomicAcqRel(Module &M,Instruction *start,bool enclave, SmallPtrSet<BasicBlock*,1>& visited_atomic_acqrel) {
            Function * RMS_Final_Atomic_AcqRel = M.getFunction("RMS_Final_Atomic_AcqRel");
            assert(RMS_Final_Atomic_AcqRel && "Module contains RMS_Initial_Atomic_AcqRel but not RMS_Final_Atomic_AcqRel");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_acqrel.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_Atomic_AcqRel) {
                        //Mark it and return
                        if (!enclave)
                            createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial release not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Atomic_AcqRel not followed by RMS_Final_Atomic_AcqRel @" << parent->getName() << "\n");

            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalAtomicAcqRel(M,&*(succ->begin()),enclave,visited_atomic_acqrel);
        }

        void markInitialAtomicAcqRel(Module &M) {
            Function * RMS_Initial_Atomic_AcqRel = M.getFunction("RMS_Initial_Atomic_AcqRel");
            if (!RMS_Initial_Atomic_AcqRel) {
                VERBOSE_PRINT("No atomic_acqrel to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_Atomic_AcqRel->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Find whether it is enclave
                    bool enclave;
                    if (call->getNumArgOperands() > 2)
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MOXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalAtomicAcqRel(M,call,enclave,temp);
                }
            }
        }

        void markNextFinalSemWait(Module &M,Instruction *start, SmallPtrSet<BasicBlock*,1>& visited_sem_wait) {
            Function * RMS_Final_SemWait = M.getFunction("RMS_Final_SemWait");
            assert(RMS_Final_SemWait && "Module contains RMS_Initial_SemWait but not RMS_Final_SemWait");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_sem_wait.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_SemWait) {
                        //Mark it and return
                        createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial release not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_SemWait not followed by RMS_Final_SemWait @" << parent->getName() << "\n");

            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalSemWait(M,&*(succ->begin()),visited_sem_wait);
        }

        void markInitialSemWait(Module &M) {
            Function * RMS_Initial_SemWait = M.getFunction("RMS_Initial_SemWait");
            if (!RMS_Initial_SemWait) {
                VERBOSE_PRINT("No semwaits to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_SemWait->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Mark it
                    createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalSemWait(M,call,temp);
                }
            }
        }

        void markNextFinalSemSignal(Module &M,Instruction *start, SmallPtrSet<BasicBlock*,1>& visited_sem_signal) {
            Function * RMS_Final_SemSignal = M.getFunction("RMS_Final_SemSignal");
            assert(RMS_Final_SemSignal && "Module contains RMS_Initial_SemSignal but not RMS_Final_SemSignal");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_sem_signal.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_SemSignal) {
                        //Mark it and return
                        createDummyCall(beginXDRF,call,false,TRACE_NUMBER);
                        createDummyCall(endNDRF,call,false,TRACE_NUMBER);
                        return;
                    }
                }
                inst++;
            }
            //If we finish a basicblock, it MUST have atleast 1 successor. Otherwise the RMS calls are incorrectly used
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial release not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_SemSignal not followed by RMS_Final_SemSignal @" << parent->getName() << "\n");

            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalSemSignal(M,&*(succ->begin()),visited_sem_signal);
        }

        void markInitialSemSignal(Module &M) {
            Function * RMS_Initial_SemSignal = M.getFunction("RMS_Initial_SemSignal");
            if (!RMS_Initial_SemSignal) {
                VERBOSE_PRINT("No semsignals to mark\n");
                return;
            }
                
            for (auto potentialcall : RMS_Initial_SemSignal->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Mark it
                    createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
                    SmallPtrSet<BasicBlock*,1> temp;
                    markNextFinalSemSignal(M,call,temp);
                }
            }
        }

        void markParsecBarrier(Module &M) {
            Function * parsecBarrier = M.getFunction("_Z19parsec_barrier_waitP16parsec_barrier_t");
            if (!parsecBarrier) {
                VERBOSE_PRINT("No parsec_barrier to mark\n");
                return;
            }
                
            for (auto potentialcall : parsecBarrier->users()) {
                if (auto call = dyn_cast<CallInst>(potentialcall)) {
                    //Mark it
                    createDummyCall(endXDRF,call,true,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,true,TRACE_NUMBER);
                    createDummyCall(endXDRF,call,TRACE_NUMBER);
                    createDummyCall(beginNDRF,call,TRACE_NUMBER);
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

        //Sets dummy to point to a function with name and a dummy implementation
      
        Function *createDummyFunction(string name, Module &M) {
            if (M.getFunction(name))
                return M.getFunction(name);
            //assert(!M.getFunction(name) && "Error creating dummy function, a function with that name already existed");
            Function *toReturn =
                cast<Function>(M.getOrInsertFunction(name,
                                                     FunctionType::get(Type::getVoidTy(getGlobalContext()),
                                                                       true)));
            toReturn->addFnAttr(Attribute::NoInline);
            toReturn->addFnAttr(Attribute::NoUnwind);
            toReturn->addFnAttr(Attribute::UWTable);
            toReturn->addFnAttr(Attribute::OptimizeNone);
            BasicBlock *block = BasicBlock::Create(getGlobalContext(),
                                                   "entry", toReturn);
            IRBuilder<true, NoFolder> builder(block);
            // //Use a redundant add as a no-op
            // builder.CreateBinOp(Instruction::Add,
            // 		    ConstantInt::get(getGlobalContext(),APInt(32,1)),
            // 		    ConstantInt::get(getGlobalContext(),APInt(32,1)));
            builder.CreateCall(InlineAsm::get(FunctionType::get(Type::getVoidTy(getGlobalContext()),
                                                                false),
                                              "nop","~{dirflag},~{fpsr},~{flags}",true));
            builder.CreateRetVoid();
            return toReturn;
        }

        void createDummyCall(Function* fun, Instruction* insertBef, int arg) {
            createDummyCall(fun,insertBef,true,arg);
        }
        
        void createDummyCall(Function* fun, Instruction* insertBef, bool before, int arg) {
            vector<Value*> arglist;
            arglist.push_back(ConstantInt::get(getGlobalContext(),APInt(32,arg)));
            ArrayRef<Value*> args(arglist);
            
            CallInst* markCall = CallInst::Create(fun,args);
            if (before)
                markCall->insertBefore(insertBef);
            else
                markCall->insertAfter(insertBef);
        }
    };
}

char MarkRMSRegions::ID = 0;
static RegisterPass<MarkRMSRegions> Z("mark-rms",
				       "Marks nDRF and XDRF regions on RMS calls",
				       true,
				       true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
