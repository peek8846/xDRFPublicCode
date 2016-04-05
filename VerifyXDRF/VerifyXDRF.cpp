//===- Identify xDRF regions in non-structured parallel applications ------===//
//
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include <sstream>
#include <iostream>
#include <string>
#include <stack>
#include <set>
#include <queue>
#include <list>
#include <map>
#include <utility>
#include <algorithm>
#include <map>


#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/APInt.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/NoFolder.h"


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"
//#include "llvm/Support/InstIterator.h"


//#include "../Utils/SkelUtils/CallingDAE.cpp"
//#include "../Utils/SkelUtils/MetadataInfo.h"

#define LIBRARYNAME "VerifyXDRF"
#define PRINTSTREAM errs() // raw_ostream

#define PRINT_DEBUG PRINTSTREAM << "VerifyXDRF: "
#define PRINT_RESULTS PRINTSTREAM << indent

#define DEBUG_VERIFY(X) DEBUG_WITH_TYPE("verify-xdrf", PRINT_DEBUG << X)
#define PRINT_VERIFY(X) DEBUG_WITH_TYPE("verify-xdrf", PRINT_RESULTS << X << "\n")

#define VERBOSE_VERIFY(X) DEBUG_WITH_TYPE("verify-xdrf-verbose", PRINT_DEBUG << X)

#define MONXDRF 0
#define MOXDRF 1

using namespace llvm;
using namespace std;

//static cl::opt<bool> SplitLibrary(
//    "split-lib",
//    cl::desc("Enable splitting around library calls"));


namespace {
    struct VerifyXDRF : public ModulePass {
        static char ID;
        VerifyXDRF() : ModulePass(ID) {}

    public:
        int DR_ID;
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
        }

        virtual bool runOnModule(Module &M) {
            // Find the functions that are spawned by pthread_create
            // These functions can be threads
            SmallPtrSet<Function*,16> thrdFunctions;
            assert(M.getFunction("pthread_create") && "Module does not spawn threads.");
            Function *pthCreate = M.getFunction("pthread_create");
            for (auto pt = pthCreate->users().begin(); pt != pthCreate->users().end(); ++pt) {
                if (isa<CallInst>(*pt)) {
                    CallInst *callsite = dyn_cast<CallInst>(*pt); // pthread_create call
                    Value *funcOp = callsite->getArgOperand(2); // operand for spawned function
                    Value *stripFuncOp = funcOp->stripPointerCasts();
                    assert(Function::classof(stripFuncOp) && "Could not dereive function");
                    Function *spawnFunc = dyn_cast<Function>(stripFuncOp); // spawned function
                    DEBUG_VERIFY("Function used by pthread_create found: " << spawnFunc->getName() << "\n");
                    thrdFunctions.insert(spawnFunc);
                }
            }

            //xDRF annotation functions
            bNDRF = M.getFunction("begin_NDRF"); //will be analyzed
            eNDRF = M.getFunction("end_NDRF"); //will be analyzed
            bXDRF = M.getFunction("begin_XDRF");
            eXDRF = M.getFunction("end_XDRF");
            eNDRFB = M.getFunction("end_NDRF_BARRIER"); //will be analyzed
            //RMS calls
            RMSIAcq = M.getFunction("RMS_Initial_Acq"); //will be analyzed
            RMSICSig = M.getFunction("RMS_Initial_CondSignal"); //will be analyzed
            RMSICBCast = M.getFunction("RMS_Initial_CondBCast"); //will be analyzed
            RMSISSig = M.getFunction("RMS_Initial_SemSignal"); //will be analyzed
            RMSICWait = M.getFunction("RMS_Initial_CondWait"); //will be analyzed
            RMSISWait = M.getFunction("RMS_Initial_SemWait"); //will be analyzed
            RMSFSSig = M.getFunction("RMS_Final_SemSignal"); //will be analyzed
            RMSFSWait = M.getFunction("RMS_Final_SemWait"); //will be analyzed
            //RMSIRel = M.getFunction("RMS_Initial_Release");
            RMSFRel = M.getFunction("RMS_Final_Release");
            RMSIBar = M.getFunction("RMS_Initial_Barrier");
            RMSFBar = M.getFunction("RMS_Final_Barrier"); //will be analyzed

            assert(bNDRF && eNDRF && eXDRF && eNDRFB &&
                   RMSIAcq && RMSFRel && RMSIBar && RMSFBar &&
                   "Module does not contain all necessary annotation and RMS calls");

            analyzeBeginNDRF();
            analyzeEndNDRF();
            analyzeEndBarrier();
            analyzeRMSInitialAcq();
            analyzeRMSFinalBarrier();

            calcResults();
            printResults(M);

            return false;
        }
    private:

        string indent = "";
        
        void setIndentLevel(int i) {
            indent = "";
            for (int j = 0; j < i; ++j)
                indent += "  ";
        }

        void calcResults() {
            numNDRF = allRegions.size();
            for (int i : allRegions) {
                if (regionXDRF[i]) {
                    if (regionALIGNED[i])
                        if (regionXDRFCORRECT[i])
                            markedXDRF_correct++;
                        else
                            if (regionBARRIERCORRECT[i])
                                markedXDRF_foundNXDRF++;
                            else
                                markedXDRF_foundBARRIER++;
                    else
                        markedXDRF_butnotfound++;
                } else {
                    if (regionBARRIER[i]) {
                        numBarrier++;
                        if (regionALIGNED[i])
                            if (regionBARRIERCORRECT[i])
                                markedBARRIER_foundBARRIER++;
                            else {
                                if (regionXDRFCORRECT[i])
                                    markedBARRIER_foundNXDRF++;
                                else
                                    markedBARRIER_foundXDRF++;
                            }
                        else
                            markedBARRIER_butnotfound++;
                    } else {
                        if (regionALIGNED[i])
                            if (!regionBARRIERCORRECT[i])
                                markedNXDRF_foundBARRIER++;
                            else
                                if (regionXDRFCORRECT[i])
                                    markedNXDRF_correct++;
                                else
                                    markedNXDRF_foundXDRF++;
                        else
                            markedNXDRF_butnotfound++;
                    }
                }
            }
        }

        void printResults(Module &M) {
            DEBUG_VERIFY("Printing results for: " << M.getName() << "\n");
            setIndentLevel(1);
            PRINT_VERIFY("Incorrect results:");
            setIndentLevel(2);
            //Class: incorrect result
            PRINT_VERIFY("Incorrectly enclave nDRFs: " << markedXDRF_foundNXDRF);
            PRINT_VERIFY("Incorrectly non-barrier enclave nDRFs: " << markedXDRF_foundBARRIER);
            PRINT_VERIFY("Incorrectly non-enclave nDRFs: " << markedNXDRF_foundXDRF);
            PRINT_VERIFY("Incorrectly non-enclave barrier nDRFs: " << markedBARRIER_foundXDRF);
            //Class: marking inaccuracy
            setIndentLevel(1);
            PRINT_VERIFY("Inaccurate marking:");
            setIndentLevel(2);
            PRINT_VERIFY("Marked enclave nDRFs with no RMS call: " << markedXDRF_butnotfound);
            PRINT_VERIFY("Marked non-enclave nDRFs with no RMS call: " << markedNXDRF_butnotfound);
            PRINT_VERIFY("Marked barrier nDRFs with no RMS call: " << markedBARRIER_butnotfound);
            PRINT_VERIFY("XDRF RMS locks with no marking: " << foundXDRF_butnotmarked);
            PRINT_VERIFY("nXDRF RMS locks with no marking: " << foundNXDRF_butnotmarked);
            PRINT_VERIFY("RMS barriers with no marking: " << foundBARRIER_butnotmarked);
            PRINT_VERIFY("Semaphore signals with no marking: " << foundSSIG_butnotmarked);
            PRINT_VERIFY("Semaphore waits with no marking: " << foundSWAIT_butnotmarked);
            //Class: analysis inaccuracy
            setIndentLevel(1);
            PRINT_VERIFY("Inaccurate analysis:");
            setIndentLevel(2);
            PRINT_VERIFY("Marked barrier nDRFs with non-barrier non-enclave RMS call: " << markedBARRIER_foundNXDRF);
            PRINT_VERIFY("Marked non-enclave nDRFs with barrier RMS call: " << markedNXDRF_foundBARRIER);
            //PRINT_VERIFY("Marked barrier nDRFs with non-barrier RMS call: " << markedBARRIER_foundNBARRIER);
            //Class: correct behavior
            setIndentLevel(1);
            PRINT_VERIFY("Correct analysis:");
            setIndentLevel(2);
            PRINT_VERIFY("Correctly marked enclave NDRFs: " << markedXDRF_correct);
            PRINT_VERIFY("Correctly marked non-enclave NDRFs: " << markedNXDRF_correct);
            PRINT_VERIFY("Correctly marked non-barrier NDRFs: " << markedNBARRIER_foundNBARRIER);
            PRINT_VERIFY("correctly marked barrier NDRFs: " << markedBARRIER_foundBARRIER);
            setIndentLevel(0);
            PRINT_VERIFY("--------------------------------------------------------");
            setIndentLevel(1);
            PRINT_VERIFY("Statistics:");
            setIndentLevel(2);
            PRINT_VERIFY("Num of marked nDRF regions: " << numNDRF);
            PRINT_VERIFY("Num of enclave nDRF regions: " << (markedXDRF_correct+markedXDRF_foundNXDRF+markedXDRF_butnotfound));
            PRINT_VERIFY("Percentage of nDRF regions correctly enclave: " << ((float) markedXDRF_correct / (float) numNDRF)*100.0);
            PRINT_VERIFY("Percentage of nDRF regions incorrectly enclave: " << ((float) markedXDRF_foundNXDRF / (float) numNDRF)*100.0);
            PRINT_VERIFY("Percentage of enclave regions correctly enclave: " << ((float) markedXDRF_correct / (float) (markedXDRF_correct+foundXDRF_butnotmarked+markedNXDRF_foundXDRF))*100.0);
            PRINT_VERIFY("Num of found barriers: " << numBarrier);
        }
        
        //xDRF annotation functions
        Function *bNDRF, //will be analyzed
            *eNDRF, //will be analyzed
            *bXDRF,
            *eXDRF,
            *eNDRFB; //will be analyzed
        //RMS calls
        Function *RMSIAcq, //will be analyzed
        //*RMSIRel,
            *RMSFRel,
            *RMSIBar,
            *RMSFBar,
            *RMSICSig,
            *RMSICBCast,
            *RMSISSig, //will be analyzed
            *RMSICWait,
            *RMSISWait, //will be analyzed
            *RMSFSSig,
            *RMSFSWait;
        
        set<int> allRegions;
        map<int,bool> regionXDRF;
        map<int,bool> regionXDRFCORRECT;
        map<int,bool> regionBARRIER;
        map<int,bool> regionBARRIERCORRECT;
        map<int,bool> regionALIGNED;

        //misc
        int markedBARRIER_foundXDRF = 0;
        int markedBARRIER_foundNXDRF = 0;
        int markedXDRF_foundBARRIER = 0;
        int markedNXDRF_foundBARRIER = 0;
        //Counters to track for begin_NDRF analysis
        int markedXDRF_foundNXDRF = 0;
        int markedNXDRF_foundXDRF = 0;
        int markedXDRF_correct = 0;
        int markedNXDRF_correct = 0;
        int markedXDRF_butnotfound = 0;
        int markedNXDRF_butnotfound = 0;
        int numNDRF = 0;

        int getIndex(CallInst* call) {
            return dyn_cast<ConstantInt>(call->getArgOperand(0))->getZExtValue();
        }

        void analyzeBeginNDRF() {
            
            for (User *use : bNDRF->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    // Figure out if the xDRF pass maks is as xDRF or not.
                    bool xDRF = true;
                    BasicBlock::iterator prevInst = BasicBlock::iterator(call);
                    if (prevInst != call->getParent()->begin()) {
                        prevInst--;
                        assert(isa<CallInst>(prevInst) &&
                               (dyn_cast<CallInst>(prevInst))->getCalledValue()->stripPointerCasts() == eXDRF &&
                               "begin_NDRF preceded by call that is not end_XDRF");
                        xDRF = false;
                    }
                    //numNDRF++;
                    allRegions.insert(getIndex(call));
                    regionXDRF[getIndex(call)] = xDRF;

                    // Check What kind of RMS call there is
                    BasicBlock* prevBlock = call->getParent()->getSinglePredecessor();
                    bool found = false;
                    bool correct = true;
                    regionALIGNED[getIndex(call)] = false;
                    for (Instruction &inst : prevBlock->getInstList()) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&inst)) {
                            if (call2->getCalledValue()->stripPointerCasts() == RMSIAcq) {
                                regionALIGNED[getIndex(call)] = true;
                                if (dyn_cast<ConstantInt>(call2->getArgOperandUse(1).get())->getZExtValue() == MONXDRF)
                                    regionXDRFCORRECT[getIndex(call)] = !xDRF;
                                else
                                    regionXDRFCORRECT[getIndex(call)] = xDRF;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSISWait) {
                                regionALIGNED[getIndex(call)] = true;
                                regionXDRFCORRECT[getIndex(call)] = !xDRF;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSIBar) {
                                regionALIGNED[getIndex(call)] = true;
                                regionXDRFCORRECT[getIndex(call)] = !xDRF;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSISSig) {
                                regionALIGNED[getIndex(call)] = true;
                                regionXDRFCORRECT[getIndex(call)] = !xDRF;
                            }
                        }
                    }
                    // if (found) {
                    //     if (correct) {
                    //         if (xDRF) {
                    //             markedXDRF_correct++;
                    //         } else {
                    //             VERBOSE_VERIFY("Detected mNEfNE in bb: " << call->getParent()->getName() << "\n");
                    //             markedNXDRF_correct++;
                    //         }
                    //     } else {
                    //         if (xDRF) {
                    //             VERBOSE_VERIFY("Detected mXfNX in bb: " << call->getParent()->getName() << "\n");
                    //             markedXDRF_foundNXDRF++;
                    //         } else {
                    //             VERBOSE_VERIFY("Detected mNXfX in bb: " << call->getParent()->getName() << "\n");
                    //             markedNXDRF_foundXDRF++;
                    //         }
                    //     }
                    // } else if (xDRF) {
                    //     VERBOSE_VERIFY("Detected mXnf in bb: " << call->getParent()->getName() << "\n");
                    //     markedXDRF_butnotfound++;
                    // } else {
                    //     VERBOSE_VERIFY("Detected mNXnf in bb: " << call->getParent()->getName() << "\n");
                    //     markedNXDRF_butnotfound++;
                    // }
                }
            }
        }

        //Counters to track for end_NDRF analysis
        int markedNBARRIER_foundNBARRIER = 0;
        int markedNBARRIER_foundBARRIER = 0;
        int markedNBARRIER_butnotfound = 0;

        void analyzeEndNDRF() {
            
            for (User *use : eNDRF->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    regionBARRIER[getIndex(call)] = false;

                    for (Instruction &inst : nextBlock->getInstList()) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&inst)) {
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFRel) {
                                regionBARRIERCORRECT[getIndex(call)] = true;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFSSig) {
                                regionBARRIERCORRECT[getIndex(call)] = true;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFSWait) {
                                regionBARRIERCORRECT[getIndex(call)] = true;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFBar) {
                                regionBARRIERCORRECT[getIndex(call)] = false;
                            }
                        }
                    }
                    // if (found) {
                    //     if (correct) {
                    //         VERBOSE_VERIFY("Detected mNBfB in bb: " << call->getParent()->getName() << "\n");
                    //         markedNBARRIER_foundNBARRIER++;
                    //     } else {
                    //         markedNBARRIER_foundBARRIER++;
                    //     }
                    // } else {
                    //     VERBOSE_VERIFY("Detected mNBnf in bb: " << call->getParent()->getName() << "\n");
                    //     markedNBARRIER_butnotfound++;
                    // }
                }
            }
        }
        
        //Counters to track for end_NDRF_BARRIER analysis
        int markedBARRIER_foundNBARRIER = 0;
        int markedBARRIER_foundBARRIER = 0;
        int markedBARRIER_butnotfound = 0;

        void analyzeEndBarrier() {
            
            for (User *use : eNDRFB->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    regionBARRIER[getIndex(call)] = true;
                    for (Instruction &inst : nextBlock->getInstList()) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&inst)) {
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFRel) {
                                regionBARRIERCORRECT[getIndex(call)] = false;
                            }
                            if (call2->getCalledValue()->stripPointerCasts() == RMSFBar) {
                                regionBARRIERCORRECT[getIndex(call)] = true;
                            }
                        }
                    }
                    // if (found) {
                    //     if (correct) {
                    //         markedBARRIER_foundBARRIER++;
                    //     } else {
                    //         VERBOSE_VERIFY("Detected mBfNB in bb: " << call->getParent()->getName() << "\n");
                    //         markedBARRIER_foundNBARRIER++;
                    //     }
                    // } else {
                    //     VERBOSE_VERIFY("Detected mBnf in bb: " << call->getParent()->getName() << "\n");
                    //     markedBARRIER_butnotfound++;
                    // }
                }
            }
        }

        //Counters to track for end_NDRF_BARRIER analysis
        int foundXDRF_butnotmarked = 0;
        int foundNXDRF_butnotmarked = 0;

        void analyzeRMSInitialAcq() {
            
            for (User *use : RMSIAcq->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
                    bool xDRF = true;
                    if (dyn_cast<ConstantInt>(call->getArgOperandUse(1).get())->getZExtValue() == 0)
                        xDRF = false;
                    bool marked = false;

                    if (nextBlock) {
                        BasicBlock::iterator nextBlockInst = nextBlock->begin();
                        if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                            if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                marked = true;
                        }
                        nextBlockInst++;
                        if (nextBlockInst != nextBlock->end())
                            if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                                if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                    marked = true;
                            }
                    }
                    if (!marked) {
                        if (xDRF) {
                            VERBOSE_VERIFY("Detected fXnm in bb: " << call->getParent()->getName() << "\n");
                            foundXDRF_butnotmarked++;
                        } else {
                            VERBOSE_VERIFY("Detected fNXnm in bb: " << call->getParent()->getName() << "\n");   
                            foundNXDRF_butnotmarked++;
                        }
                    }
                }
            }
        }

        //Counters to track for end_NDRF_BARRIER analysis
        int foundBARRIER_butnotmarked = 0;

        int numBarrier = 0;
        void analyzeRMSFinalBarrier() {
            
            for (User *use : RMSFBar->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    numBarrier++;

                    BasicBlock* prevBlock = call->getParent()->getSinglePredecessor();
                    
                    bool marked = false;

                    if (prevBlock) {
                        BasicBlock::reverse_iterator prevBlockInst = prevBlock->rbegin();
                        ++prevBlockInst;
                        if (auto call = dyn_cast<CallInst>(&(*prevBlockInst))) {
                            if (call->getCalledValue()->stripPointerCasts() == bXDRF)
                                marked = true;
                            if (call->getCalledValue()->stripPointerCasts() == eNDRFB)
                                marked = true;
                            if (call->getCalledValue()->stripPointerCasts() == eNDRF)
                                marked = true;
                        }
                    }

                    

                    if (!marked) {
                        VERBOSE_VERIFY("Detected fBnm in bb: " << call->getParent()->getName() << "\n");   
                        foundBARRIER_butnotmarked++;
                    }
                }
            }
        }

        // //Counters to track for SIGNAL analysis
        // int foundCSIGNAL_butnotmarked = 0;

        // void analyzeRMSCSignal() {
        //     for (User *use : RMSICSig->users()) {
        //         if (auto call = dyn_cast<CallInst>(use)) {
        //             BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
        //             bool marked = false;

        //             if (nextBlock) {
        //                 BasicBlock::iterator nextBlockInst = nextBlock->begin();
        //                 if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                     if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                         marked = true;
        //                 }
        //                 nextBlockInst++;
        //                 if (nextBlockInst != nextBlock->end())
        //                     if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                         if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                             marked = true;
        //                     }
        //             }
        //             if (!marked) {
        //                 VERBOSE_VERIFY("Detected fCSnm in bb: " << call->getParent()->getName() << "\n");
        //                 foundCSIGNAL_butnotmarked++;
        //             }
        //         }
        //     }
        //     for (User *use : RMSICBCast->users()) {
        //         if (auto call = dyn_cast<CallInst>(use)) {
        //             BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
        //             bool marked = false;

        //             if (nextBlock) {
        //                 BasicBlock::iterator nextBlockInst = nextBlock->begin();
        //                 if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                     if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                         marked = true;
        //                 }
        //                 nextBlockInst++;
        //                 if (nextBlockInst != nextBlock->end())
        //                     if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                         if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                             marked = true;
        //                     }
        //             }
        //             if (!marked) {
        //                 VERBOSE_VERIFY("Detected fCBCnm in bb: " << call->getParent()->getName() << "\n");
        //                 foundCSIGNAL_butnotmarked++;
        //             }
        //         }
        //     }
        // }

        // int foundCWAIT_butnotmarked = 0;

        // void analyzeRMSCWait() {
        //     for (User *use : RMSICWait->users()) {
        //         if (auto call = dyn_cast<CallInst>(use)) {
        //             BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
        //             bool marked = false;

        //             if (nextBlock) {
        //                 BasicBlock::iterator nextBlockInst = nextBlock->begin();
        //                 if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                     if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                         marked = true;
        //                 }
        //                 // nextBlockInst++;
        //                 // if (nextBlockInst != nextBlock->end())
        //                 //     if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
        //                 //         if (call->getCalledValue()->stripPointerCasts() == bNDRF)
        //                 //             marked = true;
        //                 //     }
        //             }
        //             if (!marked) {
        //                 VERBOSE_VERIFY("Detected fCWnm in bb: " << call->getParent()->getName() << "\n");
        //                 foundCWAIT_butnotmarked++;
        //             }
        //         }
        //     }
        // }

        int foundSSIG_butnotmarked = 0;

        void analyzeRMS_Initial_SemSignal() {
            for (User *use : RMSISSig->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
                    bool marked = false;

                    if (nextBlock) {
                        BasicBlock::iterator nextBlockInst = nextBlock->begin();
                        if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                            if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                marked = true;
                        }
                        nextBlockInst++;
                        if (nextBlockInst != nextBlock->end())
                            if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                                if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                    marked = true;
                            }
                    }
                    if (!marked) {
                        VERBOSE_VERIFY("Detected fSSnm in bb: " << call->getParent()->getName() << "\n");
                        foundSSIG_butnotmarked++;
                    }
                }
            }
        }

        int foundSWAIT_butnotmarked = 0;

        void analyzeRMS_Initial_SemWait() {
            for (User *use : RMSISWait->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    BasicBlock* nextBlock = call->getParent()->getSingleSuccessor();
                    
                    bool marked = false;

                    if (nextBlock) {
                        BasicBlock::iterator nextBlockInst = nextBlock->begin();
                        if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                            if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                marked = true;
                        }
                        nextBlockInst++;
                        if (nextBlockInst != nextBlock->end())
                            if (auto call = dyn_cast<CallInst>(nextBlockInst)) {
                                if (call->getCalledValue()->stripPointerCasts() == bNDRF)
                                    marked = true;
                            }
                    }
                    if (!marked) {
                        VERBOSE_VERIFY("Detected fSWnm in bb: " << call->getParent()->getName() << "\n");
                        foundSWAIT_butnotmarked++;
                    }
                }
            }
        }
    };
}



char VerifyXDRF::ID = 0;
static RegisterPass<VerifyXDRF> X("verify-xdrf",
                                  "Compares the XDRF annotation to existing RMS annotation, outputs statistics about correctness",
                                  false,
                                  true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
