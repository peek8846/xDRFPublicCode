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
// #include <set>
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
// #include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
// #include "llvm/IR/Attributes.h"
#include "llvm/IR/NoFolder.h"

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

namespace {

    struct MarkRMSRegions : public ModulePass {
        static char ID;
        MarkRMSRegions() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
        }
      
        virtual bool runOnModule(Module &M) {
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

            return true;
        }
    private:

        Function *beginNDRF;
        Function *endNDRF;
        Function *beginXDRF;
        Function *endXDRF;

        SmallPtrSet<BasicBlock*,1> visited_acqrelease;
        void markNextFinalRelease(Module &M,Instruction *start,bool enclave) {
            Function * RMS_Final_Release = M.getFunction("RMS_Final_Release");
            assert(RMS_Final_Release && "Module contains RMS_Initial_Acq but not RMS_Final_Release");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_acqrelease.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>(&*inst)) {
                    if (call->getCalledFunction() == RMS_Final_Release) {
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
                markNextFinalRelease(M,&*(succ->begin()),enclave);
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
                    enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(1).get())->getZExtValue() == MONXDRF;
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalRelease(M,call,enclave);
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_barrier;
        void markNextFinalBarrier(Module &M,Instruction *start) {
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
                VERBOSE_PRINT("Warning: RMS_Initial_Barrier not followed by RMS_Final_Barrier @" << parent->getName() << "\n");
            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalBarrier(M,&*(succ->begin()));
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
                    createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalBarrier(M,call);
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_atomic_acq;
        void markNextFinalAtomicAcq(Module &M,Instruction *start,bool enclave) {
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
                VERBOSE_PRINT("Warning: RMS_Initial_Atomic_Acq not followed by RMS_Final_Atomic_Acq @" << parent->getName() << "\n");
            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalAtomicAcq(M,&*(succ->begin()),enclave);
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
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MONXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalAtomicAcq(M,call,enclave);
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_atomic_release;
        void markNextFinalAtomicRelease(Module &M,Instruction *start,bool enclave) {
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
                            createDummyCall(beginXDRF,call,false,0);
                        createDummyCall(endNDRF,call,false,0);
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
                markNextFinalAtomicRelease(M,&*(succ->begin()),enclave);
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
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MONXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalAtomicRelease(M,call,enclave);
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_atomic_acqrel;
        void markNextFinalAtomicAcqRel(Module &M,Instruction *start,bool enclave) {
            Function * RMS_Final_Atomic_AcqRel = M.getFunction("RMS_Final_Atomic_AcqRel");
            assert(RMS_Final_Atomic_AcqRel && "Module contains RMS_Initial_Atomic_AcqRel but not RMS_Final_Atomic_AcqRel");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_release.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_Atomic_AcqRel) {
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
            //assert(succ_begin(parent) != succ_end(parent) && "RMS initial release not followed by RMS final release");
            if (succ_begin(parent) == succ_end(parent))
                VERBOSE_PRINT("Warning: RMS_Initial_Atomic_AcqRel not followed by RMS_Final_Atomic_AcqRel @" << parent->getName() << "\n");

            for (auto succ = succ_begin(parent);
                 succ != succ_end(parent);
                 ++succ)
                markNextFinalAtomicAcqRel(M,&*(succ->begin()),enclave);
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
                        enclave = dyn_cast<ConstantInt>(call->getArgOperandUse(2).get())->getZExtValue() == MONXDRF;
                    else
                        enclave = false; 
                    //Mark it
                    if (!enclave)
                        createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalAtomicAcqRel(M,call,enclave);
                    return;
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_semwait;
        void markNextFinalSemWait(Module &M,Instruction *start) {
            Function * RMS_Final_SemWait = M.getFunction("RMS_Final_SemWait");
            assert(RMS_Final_SemWait && "Module contains RMS_Initial_SemWait but not RMS_Final_SemWait");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_release.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_SemWait) {
                        //Mark it and return
                        createDummyCall(beginXDRF,call,false,0);
                        createDummyCall(endNDRF,call,false,0);
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
                markNextFinalSemWait(M,&*(succ->begin()));
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
                    createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalSemWait(M,call);
                    return;
                }
            }
        }

        SmallPtrSet<BasicBlock*,1> visited_semsignal;
        void markNextFinalSemSignal(Module &M,Instruction *start) {
            Function * RMS_Final_SemSignal = M.getFunction("RMS_Final_SemSignal");
            assert(RMS_Final_SemSignal && "Module contains RMS_Initial_SemSignal but not RMS_Final_SemSignal");
            BasicBlock *parent = start->getParent();
            //If someone previously handled this basicblock, return
            if (!(visited_atomic_release.insert(parent).second))
                return;
            BasicBlock::iterator inst = BasicBlock::iterator(start);
            while (inst != parent->end()) {
                if (auto call = dyn_cast<CallInst>((&*inst))) {
                    if (call->getCalledFunction() == RMS_Final_SemSignal) {
                        //Mark it and return
                        createDummyCall(beginXDRF,call,false,0);
                        createDummyCall(endNDRF,call,false,0);
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
                markNextFinalSemSignal(M,&*(succ->begin()));
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
                    createDummyCall(endXDRF,call,0);
                    createDummyCall(beginNDRF,call,0);
                    markNextFinalSemSignal(M,call);
                    return;
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
            toReturn->addFnAttr(Attribute::OptimizeNone);
            BasicBlock *block = BasicBlock::Create(getGlobalContext(),
                                                   "entry", toReturn);
            IRBuilder<true, NoFolder> builder(block);
            // //Use a redundant add as a no-op
            // builder.CreateBinOp(Instruction::Add,
            // 		    ConstantInt::get(getGlobalContext(),APInt(32,1)),
            // 		    ConstantInt::get(getGlobalContext(),APInt(32,1)));
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
