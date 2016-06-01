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
#include <stdexcept>

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
            //RMS calls
            RMSIAcq = M.getFunction("RMS_Initial_Acq"); //will be analyzed
            RMSIRel = M.getFunction("RMS_Initial_Release"); //will be analyzed
            RMSISSig = M.getFunction("RMS_Initial_SemSignal"); //will be analyzed
            RMSISWait = M.getFunction("RMS_Initial_SemWait"); //will be analyzed
            RMSIBar = M.getFunction("RMS_Initial_Barrier"); //will be analyzed
            RMSFBar = M.getFunction("RMS_Final_Barrier"); //will be analyzed

            // assert(bNDRF && eNDRF && bXDRF && eXDRF &&
            //        RMSIAcq && RMSIRel && RMSIBar && RMSFBar &&
            //        "Module does not contain all necessary annotation and RMS calls");

            assert(bNDRF && eNDRF && bXDRF && eXDRF &&
                   "Module does not have compiler markings");
            
            analyzeBeginNDRF();
            analyzeEndNDRF();
            if (RMSIAcq) {
                analyzeRMSInitialAcq();
                analyzeRMSInitialRel();
            }
            if (RMSIBar) {
                analyzeRMSInitialBarrier();
                analyzeRMSFinalBarrier();
            }
            // analyzeRMSInitialSemSignal();
            // analyzeRMSInitialSemWait();

            //calcResults();
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

        // void calcResults() {
        //     for (int i : allRegions) {
        //         if (regionXDRF[i]) {
        //             if (regionALIGNED[i])
        //                 if (regionXDRFCORRECT[i])
        //                     markedXDRF_correct++;
        //                 else
        //                     if (regionBARRIERCORRECT[i])
        //                         markedXDRF_foundNXDRF++;
        //                     else
        //                         markedXDRF_foundBARRIER++;
        //             else
        //                 markedXDRF_butnotfound++;
        //         } else {
        //             if (regionBARRIER[i]) {
        //                 numBarrier++;
        //                 if (regionALIGNED[i])
        //                     if (regionBARRIERCORRECT[i])
        //                         markedBARRIER_foundBARRIER++;
        //                     else {
        //                         if (regionXDRFCORRECT[i])
        //                             markedBARRIER_foundNXDRF++;
        //                         else
        //                             markedBARRIER_foundXDRF++;
        //                     }
        //                 else
        //                     markedBARRIER_butnotfound++;
        //             } else {
        //                 if (regionALIGNED[i])
        //                     if (!regionBARRIERCORRECT[i])
        //                         markedNXDRF_foundBARRIER++;
        //                     else
        //                         if (regionXDRFCORRECT[i])
        //                             markedNXDRF_correct++;
        //                         else
        //                             markedNXDRF_foundXDRF++;
        //                 else
        //                     markedNXDRF_butnotfound++;
        //             }
        //         }
        //     }
        // }

        void printResults(Module &M) {
            DEBUG_VERIFY("Printing results for: " << M.getName() << "\n");
            setIndentLevel(1);
            PRINT_VERIFY("Incorrect results:");
            setIndentLevel(2);
            //Class: incorrect result
            PRINT_VERIFY("Incorrectly enclave begin_ndrf: " << incorrectENCAcq);
            PRINT_VERIFY("Incorrectly enclave end_ndrf: " << incorrectENCRel);
            PRINT_VERIFY("Incorrectly non-enclave begin_ndrf: " << incorrectNENCAcq);
            PRINT_VERIFY("Incorrectly non-enclave end_ndrf: " << incorrectNENCRel);
            //Class: marking inaccuracy
            setIndentLevel(1);
            PRINT_VERIFY("Inaccurate marking:");
            setIndentLevel(2);
            PRINT_VERIFY("Unaligned enclave begin_ndrf: " << unalignedENCAcq);
            PRINT_VERIFY("Unaligned enclave end_ndrf: " << unalignedENCRel);
            PRINT_VERIFY("Unaligned non-enclave begin_ndrf: " << unalignedNENCAcq);
            PRINT_VERIFY("Unaligned non-enclave end_ndrf: " << unalignedNENCRel);
            PRINT_VERIFY("Unaligned non-enclave RMS acq: " << unalignedRMSNENCAcq);
            PRINT_VERIFY("Unaligned non-enclave RMS rel: " << unalignedRMSNENCRel);
            PRINT_VERIFY("Unaligned enclave RMS acq: " << unalignedRMSENCAcq);
            PRINT_VERIFY("Unaligned enclave RMS rel: " << unalignedRMSENCRel);
            PRINT_VERIFY("Unaligned barrier RMS acq: " << unalignedRMSBarrAcq);
            PRINT_VERIFY("Unaligned barrier RMS rel: " << unalignedRMSBarrRel);
            setIndentLevel(1);
            PRINT_VERIFY("Correct analysis:");
            setIndentLevel(2);
            PRINT_VERIFY("Correctly enclave begin_ndrf: " << correctENCAcq);
            PRINT_VERIFY("Correctly enclave end_ndrf: " << correctENCRel);
            PRINT_VERIFY("Correctly non-enclave begin_ndrf: " << correctNENCAcq);
            PRINT_VERIFY("Correctly non-enclave end_ndrf: " << correctNENCRel);
            setIndentLevel(0);
            PRINT_VERIFY("--------------------------------------------------------");
            // setIndentLevel(1);
            // PRINT_VERIFY("Statistics:");
            // setIndentLevel(2);
            // PRINT_VERIFY("Num of marked nDRF regions: " << numNDRF);
            // PRINT_VERIFY("Num of enclave nDRF regions: " << (markedXDRF_correct+markedXDRF_foundNXDRF+markedXDRF_butnotfound));
            // PRINT_VERIFY("Percentage of nDRF regions correctly enclave: " << ((float) markedXDRF_correct / (float) numNDRF)*100.0);
            // PRINT_VERIFY("Percentage of nDRF regions incorrectly enclave: " << ((float) markedXDRF_foundNXDRF / (float) numNDRF)*100.0);
            // PRINT_VERIFY("Percentage of enclave regions correctly enclave: " << ((float) markedXDRF_correct / (float) (markedXDRF_correct+foundXDRF_butnotmarked+markedNXDRF_foundXDRF))*100.0);
            //PRINT_VERIFY("Num of found barriers: " << numBarrier);
        }
        
        //xDRF annotation functions
        Function *bNDRF, //will be analyzed
            *eNDRF, //will be analyzed
            *bXDRF,
            *eXDRF;
        //RMS calls
        Function *RMSIAcq, //will be analyzed
            *RMSIRel, //will be analyzed
            *RMSIBar,
            *RMSFBar,
            *RMSISSig,
            *RMSISWait;
        
        int unalignedNENCAcq = 0;
        int unalignedNENCRel = 0;
        int unalignedENCAcq = 0;
        int unalignedENCRel = 0;
        int correctNENCRel = 0;
        int correctENCRel = 0;
        int incorrectNENCRel = 0;
        int incorrectENCRel = 0;
        int correctNENCAcq = 0;
        int incorrectNENCAcq = 0;
        int correctENCAcq = 0;
        int incorrectENCAcq = 0;

        int unalignedRMSNENCAcq = 0;
        int unalignedRMSNENCRel = 0;
        int unalignedRMSENCAcq = 0;
        int unalignedRMSENCRel = 0;
        int unalignedRMSBarrAcq = 0;
        int unalignedRMSBarrRel = 0;

        void moveIteratorUp(BasicBlock::iterator &iter) {
            if (iter != iter->getParent()->begin()) {
                iter--;
            } else {
                //assert(iter->getUniquePredecessor() && "Tried to move instruction iterator across basicblock that had more than one predecessor");
                if (iter->getParent()->getUniquePredecessor())
                    throw runtime_error("More than one preceding block in block transition");
                iter=iter->getParent()->getUniquePredecessor()->end();
                iter--;
            }
        }

        void moveIteratorDown(BasicBlock::iterator &iter) {
            BasicBlock::iterator it = iter;
            it++;
            if (it != iter->getParent()->end()) {
                iter=it;
            } else {
                if (iter->getParent()->getUniqueSuccessor())
                    throw runtime_error("More than one following block in block transition");
                //assert(iter->getUniqueSucessor() && "Tried to move instruction iterator across basicblock that had more than one sucessor");
                iter=iter->getParent()->getUniqueSuccessor()->begin();
            }
        }


        void analyzeBeginNDRF() {
            
            for (User *use : bNDRF->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    // Figure out if the xDRF pass marks it as xDRF or not.
                    bool xDRF = true;
                    BasicBlock::iterator prevInst = BasicBlock::iterator(call);
                    try {
                        moveIteratorUp(prevInst);
                        if (isa<CallInst>(prevInst) &&
                            (dyn_cast<CallInst>(prevInst))->getCalledValue()->stripPointerCasts() == eXDRF) {
                            moveIteratorUp(prevInst);
                            xDRF = false;
                        }
                        moveIteratorDown(prevInst);
                    } catch(runtime_error e) {
                        //This should not happen if delimitation is correct:
                        //Increase unaligned pred count
                        VERBOSE_VERIFY("Found a purely unaligned begin_ndrf");
                        unalignedENCAcq++;
                        continue;
                    }
                    
                    bool aligned = false;
                    bool correct = false;
                    
                    //Check for the possible surrounding RMS calls
                    //Check the instructions within this block before the xDRF call
                    for (BasicBlock::reverse_iterator iter = BasicBlock::reverse_iterator(prevInst);
                         iter != prevInst->getParent()->rend(); ++iter) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards initial acquire
                            if (call2->getCalledValue()->stripPointerCasts() == RMSIAcq) {
                                aligned=true;
                                if (dyn_cast<ConstantInt>(call2->getArgOperandUse(1).get())->getZExtValue() == MONXDRF)
                                    correct=!xDRF;
                                else
                                    correct=xDRF;
                                break;
                            }
                            //Match towards initial barrier
                            if (call2->getCalledValue()->stripPointerCasts() == RMSIBar) {
                                aligned = true;
                                correct=!xDRF;
                                break;
                            }
                        }
                    }

                    if (aligned) {
                        if (correct) {
                            if (xDRF)
                                correctENCAcq++;
                            else
                                correctNENCAcq++;
                        } else {
                            if (xDRF)
                                incorrectENCAcq++;
                            else
                                incorrectNENCAcq++;
                        }
                    } else {
                        if (xDRF)
                            unalignedENCAcq++;
                        else
                            unalignedNENCAcq++;
                    }
                    //VERBOSE_VERIFY((*call) << " - marked: " << (xDRF ? "enclave" : "non-enclave") << " aligned: " << (aligned ? "true" : "false") << " correct: " << (correct ? "true" : "false") << "\n");
                }
            }
        }

        void analyzeEndNDRF() {
            
            for (User *use : eNDRF->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    //DEBUG_VERIFY("Checking " << *call << "\n");
                    //DEBUG_VERIFY("BB is " << *(call->getParent()) << "\n");
                    // Figure out if the xDRF pass marks it as xDRF or not.
                    bool xDRF = true;
                    BasicBlock::iterator prevInst = BasicBlock::iterator(call);
                    try {
                        moveIteratorDown(prevInst);
                        if (isa<CallInst>(prevInst) &&
                            (dyn_cast<CallInst>(prevInst))->getCalledValue()->stripPointerCasts() == bXDRF) {
                            xDRF = false;
                        }
                        moveIteratorUp(prevInst);
                    } catch(runtime_error e) {
                        //This should not happen if delimitation is correct:
                        //Increase unaligned pred count
                        VERBOSE_VERIFY("Found a purely unaligned end_ndrf");
                        unalignedENCRel++;
                        continue;
                    }

                    bool aligned=false;
                    bool correct=false;

                    //Check the instructions WITHIN this block before the xDRF call for initial_acquire
                    for (BasicBlock::reverse_iterator iter = BasicBlock::reverse_iterator(prevInst);
                         iter != prevInst->getParent()->rend(); ++iter) {
                        //DEBUG_VERIFY("Checking towards " << *iter << "\n");
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards initial release
                            if (call2->getCalledValue()->stripPointerCasts() == RMSIRel) {
                                aligned=true;
                                if (dyn_cast<ConstantInt>(call2->getArgOperandUse(1).get())->getZExtValue() == MONXDRF)
                                    correct=!xDRF;
                                else
                                    correct=xDRF;
                                break;
                            }
                        }
                    }

                    if (!aligned)  {
                        //Check the instructions WITHIN this block after the xDRF call for final_barrier
                        for (BasicBlock::iterator iter = BasicBlock::iterator(prevInst);
                             iter != prevInst->getParent()->end(); ++iter) {
                            //DEBUG_VERIFY("Checking towards " << *iter << "\n");
                            if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                                //Match towards final barrier
                                if (call2->getCalledValue()->stripPointerCasts() == RMSFBar) {
                                    aligned = true;
                                    correct=!xDRF;
                                    break;
                                }
                            }
                        }
                    }
                    
                    if (aligned) {
                        if (correct) {
                            if (xDRF)
                                correctENCRel++;
                            else
                                correctNENCRel++;
                        } else {
                            if (xDRF)
                                incorrectENCRel++;
                            else
                                incorrectNENCRel++;
                        }
                    } else {
                        if (xDRF)
                            unalignedENCRel++;
                        else
                            unalignedNENCRel++;
                    }
                    //VERBOSE_VERIFY((*call) << " - marked: " << (xDRF ? "enclave" : "non-enclave") << " aligned: " << (aligned ? "true" : "false") << " correct: " << (correct ? "true" : "false") << "\n");
                }
            }
        }
        
        void analyzeRMSInitialAcq() {
            for (User *use : RMSIAcq->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                    
                    bool xDRF = true;
                    if (dyn_cast<ConstantInt>(call->getArgOperandUse(1).get())->getZExtValue() == 0)
                        xDRF = false;
                    bool marked = false;


                    //Check the instructions WITHIN this block after the marking for compiler markings
                    for (BasicBlock::iterator iter = BasicBlock::iterator(call);
                         iter != call->getParent()->end(); ++iter) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards begin_ndrf
                            if (call2->getCalledValue()->stripPointerCasts() == bNDRF) {
                                marked=true;
                                break;
                            }
                        }
                    }

                    if (!marked) {
                        if (xDRF) {
                            //VERBOSE_VERIFY("Detected fXnm in bb: " << call->getParent()->getName() << "\n");
                            unalignedRMSENCAcq++;
                        } else {
                            //VERBOSE_VERIFY("Detected fNXnm in bb: " << call->getParent()->getName() << "\n");   
                            unalignedRMSNENCAcq++;
                        }
                    }
                }
            }
        }

        void analyzeRMSInitialRel() {
            for (User *use : RMSIRel->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {
                   
                    bool xDRF = true;
                    if (dyn_cast<ConstantInt>(call->getArgOperandUse(1).get())->getZExtValue() == 0)
                        xDRF = false;
                    bool marked = false;


                    //Check the instructions WITHIN this block after the marking for compiler markings
                    for (BasicBlock::iterator iter = BasicBlock::iterator(call);
                         iter != call->getParent()->end(); ++iter) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards end_ndrf
                            if (call2->getCalledValue()->stripPointerCasts() == eNDRF) {
                                marked=true;
                                break;
                            }
                        }
                    }

                    if (!marked) {
                        if (xDRF) {
                            //VERBOSE_VERIFY("Detected fXnm in bb: " << call->getParent()->getName() << "\n");
                            unalignedRMSENCRel++;
                        } else {
                            //VERBOSE_VERIFY("Detected fNXnm in bb: " << call->getParent()->getName() << "\n");   
                            unalignedRMSNENCRel++;
                        }
                    }
                }
            }
        }

        void analyzeRMSInitialBarrier() {
            
            for (User *use : RMSIBar->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {

                    bool marked = false;

                    //Check the instructions WITHIN this block after the marking for compiler markings
                    for (BasicBlock::iterator iter = BasicBlock::iterator(call);
                         iter != call->getParent()->end(); ++iter) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards begin_ndrf
                            if (call2->getCalledValue()->stripPointerCasts() == bNDRF) {
                                marked=true;
                                break;
                            }
                        }
                    }

                    if (!marked) {
                        //VERBOSE_VERIFY("Detected fNXnm in bb: " << call->getParent()->getName() << "\n");   
                        unalignedRMSBarrAcq++;
                    }
                }
            }
        }

        void analyzeRMSFinalBarrier() {
            
            for (User *use : RMSFBar->users()) {
                if (auto call = dyn_cast<CallInst>(use)) {

                    bool marked = false;

                    //Check the instructions WITHIN this block for compiler markings
                    for (BasicBlock::reverse_iterator iter = BasicBlock::reverse_iterator(BasicBlock::iterator(call));
                         iter != call->getParent()->rend(); ++iter) {
                        if (CallInst *call2 = dyn_cast<CallInst>(&*iter)) {
                            //Match towards begin_ndrf
                            if (call2->getCalledValue()->stripPointerCasts() == eNDRF) {
                                marked=true;
                                break;
                            }
                        }
                    }

                    if (!marked) {
                        //VERBOSE_VERIFY("Detected fNXnm in bb: " << call->getParent()->getName() << "\n");   
                        unalignedRMSBarrRel++;
                    }
                }
            }
        }
        // void analyzeRMS_Initial_SemSignal() {
        //     for (User *use : RMSISSig->users()) {
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
        //                 VERBOSE_VERIFY("Detected fSSnm in bb: " << call->getParent()->getName() << "\n");
        //                 foundSSIG_butnotmarked++;
        //             }
        //         }
        //     }
        // }

        // int foundSWAIT_butnotmarked = 0;

        // void analyzeRMS_Initial_SemWait() {
        //     for (User *use : RMSISWait->users()) {
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
        //                 VERBOSE_VERIFY("Detected fSWnm in bb: " << call->getParent()->getName() << "\n");
        //                 foundSWAIT_butnotmarked++;
        //             }
        //         }
        //     }
        
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
