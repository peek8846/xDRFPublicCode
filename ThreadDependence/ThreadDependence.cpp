//=== Tracks the values that are calculated based on arguments to thread functions ==//
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

#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Pass.h"
//#include "llvm/Support/InstIterator.h"


//#include "../Utils/SkelUtils/CallingDAE.cpp"
//#include "../Utils/SkelUtils/MetadataInfo.h"

#define LIBRARYNAME "ThreadDependence"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << LIBRARYNAME": "
#define PRINT_DEBUG PRINTSTREAM << LIBRARYNAME"(debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;


namespace {
    struct ThreadDependence : public ModulePass {
        static char ID;
        ThreadDependence() : ModulePass(ID) {}

    public:
        int DR_ID;
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            // AU.addRequired<AssumptionCacheTracker>();
            // AU.addRequired<TargetLibraryInfoWrapperPass>();
            AU.addRequired<ScalarEvolutionWrapperPass>();
            AU.setPreservesAll();
        }

        virtual bool runOnModule(Module &M) {
            // Find the functions that are spawned by pthread_create
            // These functions can be threads
            SmallPtrSet<Function*,4> thrdFunctions;
            assert(M.getFunction("pthread_create") && "Module does not spawn threads.");
            findEntryPoints(M,thrdFunctions);

            //Mark all values whose values depend on a thread-starting functions argument
            VERBOSE_PRINT("Coloring argument to thread start-points...\n");
            for (Function * fun : thrdFunctions) {
                VERBOSE_PRINT("Coloring " << fun->getName() << "\n");
                for (Argument &arg : fun->getArgumentList()) {
                    trackDerivedValues(&arg);
                }
                VERBOSE_PRINT("Done coloring " << fun->getName() << "\n");
            }

            VERBOSE_PRINT("Colored a total of " << threadDependantValues.size() << " values\n");
            // DEBUG_PRINT("Colored:\n");
            // for (Value * val  : threadDependantValues) {
            //     DEBUG_PRINT(*val << "\n");
            // }

            return false;
        }

        bool dependsOnThread(Value * val) {
            LIGHT_PRINT("Checked whether " << *val << " was dependent on thread arguments... " << (threadDependantValues.count(val)!=0 ? "it was" : "it wasn't") << "\n");
            return threadDependantValues.count(val)!=0;
        }

    private:

        SmallPtrSet<Value*,256> threadDependantValues;

        //Utility: Checks wether a given callsite contains a call
        bool isNotNull(CallSite call) {
            return call.isCall() || call.isInvoke();
        }
        
        //Utility: Checks whether an instruction could be a callsite
        bool isCallSite(Instruction* inst) {
            return isNotNull(CallSite(inst));
        }

        //Functions that should never be considered for tracking
        //Don't use this too much
        set<StringRef> noAnalyzeFunctions = {
            //INTERNALLY USED FUNCTIONS
            "begin_NDRF","end_NDRF","begin_XDRF","end_XDRF",
            //RMS FUNCTIONS
            "RMS_Initial_Acq","RMS_Final_Acq","RMS_Initial_Release","RMS_Final_Release",
            "RMS_Initial_Barrier","RMS_Final_Barrier",
            "RMS_Initial_SemWait","RMS_Final_SemWait",
            "RMS_Initial_SemSignal","RMS_Final_SemSignal",
            "RMS_Initial_CondWait","RMS_Final_CondWait",
            "RMS_Initial_CondSignal","RMS_Final_CondSignal",
            "RMS_Initial_CondBCast","RMS_Final_CondBCast",
            //Takes space in debug output
            "RMS_Initialization_Done"
        };
        
        //These are the function to treat as if they spawn new
        //threads
        set<StringRef> threadFunctions = {"pthread_create"};
        
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

        //Obtains the set of functions that can be immediately called when
        //executing inst
        SmallPtrSet<Function*,1> getCalledFuns(Instruction *inst) {
            LIGHT_PRINT("Finding functions that can be called by " << *inst << "\n");
            SmallPtrSet<Function*,1> toReturn;
            SmallPtrSet<Value*,8> alreadyVisited;
            if (isCallSite(inst)) {
                LIGHT_PRINT("which is a callsite\n");
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
                        if (noAnalyzeFunctions.count(fun->getName()) == 0)
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
                    //Don't need to concern ourselves with this
                    //Special case, if we "call" inline assembly we merely need to decide whether the
                    //assembly synchronizes or not. if there is a "lock" in the aseembly then it synchronizes,
                    //otherwise it does not
                    // else if (auto inlineasm = dyn_cast<InlineAsm>(nextValue)) {
                    //     LIGHT_PRINT("Could call assembly\n");
                    //     if (inlineasm->getAsmString().find("lock") != string::npos) {
                    //         LIGHT_PRINT("Could call atomic assembly\n");
                    //         toReturn.insert(DummyATOMICASMFunc);
                    //         LIGHT_PRINT("Returned as " << DummyATOMICASMFunc->getName() << "\n");
                    //     }
                    // }
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
                                    if (noAnalyzeFunctions.count(fun.getName()) == 0)
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

        
        
        //Gets the possible highes-level pointers who can only refer to locations that the argument could refer to
        map<Value*,SmallPtrSet<Value*,1> > getBaseOfPointerDynamic;
        SmallPtrSet<Value*,1> getBaseOfPointer(Value * pointer) {
            DEBUG_PRINT("Finding base pointer for " << *pointer << "\n");
            SmallPtrSet<Value*,1> toReturn;
            if (!isa<PointerType>(pointer->getType())) {
                DEBUG_PRINT("Wasn't a pointer\n");
                return toReturn;
            }
            if (getBaseOfPointerDynamic.count(pointer) != 0) {
                DEBUG_PRINT("Resolved dynamically\n");
                return getBaseOfPointerDynamic[pointer];
            }
            
            getBaseOfPointerDynamic[pointer]=toReturn;
            
            Value * stripped = pointer->stripInBoundsConstantOffsets();
            DEBUG_PRINT("Stripped to " << *stripped << "\n");

            if (auto load = dyn_cast<LoadInst>(stripped)) {
                DEBUG_PRINT("Was pointer loaded from " << *(load->getPointerOperand()) << "\n");
                SmallPtrSet<Value*,1> interResult = getBaseOfPointer(load->getPointerOperand());
                toReturn.insert(interResult.begin(),interResult.end());
            }
            if (auto arg = dyn_cast<Argument>(stripped)) {
                for (auto user : arg->getParent()->users()) {
                    if (Instruction *inst = dyn_cast<Instruction>(user)) {
                        if (isCallSite(inst)) {
                            CallSite call(inst);
                            DEBUG_PRINT("Was argument, one parameter is: " << call.getArgument(arg->getArgNo()) << "\n");
                            SmallPtrSet<Value*,1> interResult=getBaseOfPointer(call.getArgument(arg->getArgNo()));
                            toReturn.insert(interResult.begin(),interResult.end());
                        }
                    }
                }
            }
            if (auto phi = dyn_cast<PHINode>(stripped)) {
                for (Use &use : phi->incoming_values()) {
                    DEBUG_PRINT("Was phinode with incoming value " << *(use.get()) << "\n");
                    SmallPtrSet<Value*,1> interResult = getBaseOfPointer(use.get());
                    toReturn.insert(interResult.begin(),interResult.end());
                }
            }
            if (auto gep = dyn_cast<GetElementPtrInst>(stripped)) {
                DEBUG_PRINT("Was dynamic GEP " << *(gep) << "\n");
                SmallPtrSet<Value*,1> interResult = getBaseOfPointer(gep->getPointerOperand());
                toReturn.insert(interResult.begin(),interResult.end());

                // LIGHT_PRINT("Attempting to get base pointer through a non-constant GEP\n");
                // ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>(*(gep->getParent()->getParent())).getSE();
                // // const SCEV* scev = SE.getSCEV(gep);
                // // LIGHT_PRINT("SCEV got " << *scev << "\n");
                // SmallPtrSet<Value*,1> basePointers = getBaseOfPointer(gep->getPointerOperand());

                // LIGHT_PRINT("Got base pointers for " << *gep << "\n");

                // for (Value* basePointer : basePointers) {
                //     LIGHT_PRINT("Possible base pointer " << *basePointer << " being examined for domination\n");
                //     Type * basePointerType = basePointer->getType();
                //     LIGHT_PRINT("Which has type: " << *basePointerType << " (which has type " << typeid(*basePointerType).name() << ")\n");
                //     LIGHT_PRINT("Checking to see if we can acquire the possible range for the pointer...\n");
                //     int elementCount = -1;
                //     int dominatorIndex = 0;
                //     if (basePointerType->isStructTy()) {
                //         LIGHT_PRINT("Was a struct with " << basePointerType->getStructNumElements() << " elements\n");
                //         elementCount = basePointerType->getStructNumElements();
                //     }
                //     else if (basePointerType->isArrayTy()) {
                //         LIGHT_PRINT("Was a struct with " << basePointerType->getArrayNumElements() << " elements\n");
                //         elementCount = basePointerType->getArrayNumElements();
                //     }
                //     else if (basePointerType->isVectorTy()) {
                //         LIGHT_PRINT("Was a struct with " << basePointerType->getVectorNumElements() << " elements\n");
                //         elementCount = basePointerType->getVectorNumElements();
                //     }
                //     else if (basePointerType->isPointerTy()) {
                //         dominatorIndex = 1;
                //         LIGHT_PRINT("Was a pointer type pointing at " << *(basePointerType->getPointerElementType()) << "\n");
                //         Type * dereferedPointer = basePointerType->getPointerElementType();
                //         LIGHT_PRINT("Got " << *dereferedPointer << ", checking size again\n");
                //         if (dereferedPointer->isStructTy()) {
                //             LIGHT_PRINT("Was a struct with " << dereferedPointer->getStructNumElements() << " elements\n");
                //             elementCount = dereferedPointer->getStructNumElements();
                //         }
                //         else if (dereferedPointer->isArrayTy()) {
                //             LIGHT_PRINT("Was a struct with " << dereferedPointer->getArrayNumElements() << " elements\n");
                //             elementCount = dereferedPointer->getArrayNumElements();
                //         }
                //         else if (dereferedPointer->isVectorTy()) {
                //             LIGHT_PRINT("Was a struct with " << dereferedPointer->getVectorNumElements() << " elements\n");
                //             elementCount = dereferedPointer->getVectorNumElements();
                //         } else {
                //             LIGHT_PRINT("Could not\n");
                //         }
                //     } else {
                //         LIGHT_PRINT("Could not\n");
                //     }
                    
                //     if (elementCount > -1) {
                //         LIGHT_PRINT("Checking if GEP dominates pointer range\n");
                //         auto index = gep->idx_begin();
                //         // for (int i = 0; i < dominatorIndex;  ++i) {index++;};
                //         DEBUG_PRINT("Checking index " << **index << "\n");
                //         const SCEV* dominatorIndexScev = SE.getSCEV(*index);
                //         LIGHT_PRINT("Got scev " << *dominatorIndexScev << "\n");
                //         if (auto cast = dyn_cast<SCEVCastExpr>(dominatorIndexScev)) {
                //             LIGHT_PRINT("Was cast from " << *(cast->getOperand()) << "\n");
                //             LIGHT_PRINT("Which was a " << cast->getOperand()->getSCEVType() << "\n");
                //         }

                //         ConstantRange indexRange = SE.getSignedRange(dominatorIndexScev);
                //         LIGHT_PRINT("Has range " << indexRange << "\n");
                //         if (indexRange == ConstantRange(APInt(indexRange.getUnsignedMin().getBitWidth(),0),
                //                                         APInt(indexRange.getUnsignedMin().getBitWidth(),elementCount))) {
                //             LIGHT_PRINT("which dominated pointer range\n");
                //             toReturn.insert(basePointer);
                //         }
                //         else {
                //             LIGHT_PRINT("which did not dominate pointer range\n");
                //         }
                //     }
                // }
                
                // //assert(false && "UNIMPLEMENTED - GEP SCEV resolution");
                
                // if (basePointers.size() == 0) {
                //     LIGHT_PRINT("Found no base pointers\n");
                // }
                

            }
            
            if (auto glob = dyn_cast<GlobalVariable>(stripped)) {
                DEBUG_PRINT("Was a global, plainly\n");
                toReturn.insert(glob);
            }
            if (auto alloc = dyn_cast<AllocaInst>(stripped)) {
                DEBUG_PRINT("Was an alloca, plainly\n");
                toReturn.insert(alloc);
            }
            if (auto inst = dyn_cast<Instruction>(stripped)) {
                
                SmallPtrSet<Function*,1> calledFuns=getCalledFuns(inst);
                for (Function * calledFun : calledFuns) {
                    if (calledFun->getName().equals("malloc") ||
                        calledFun->getName().equals("MyMalloc")
                        ) {
                        DEBUG_PRINT("Was an allocation\n");
                        toReturn.insert(inst);
                    }
                    else {
                        for (auto it = inst_begin(calledFun);
                             it != inst_end(calledFun); ++it) {
                            if (auto ret = dyn_cast<ReturnInst>(&*it)) {
                                if (ret->getReturnValue()) {
                                    DEBUG_PRINT("Was call to a function that could return " << ret->getReturnValue() << "\n");
                                    SmallPtrSet<Value*,1> interResult = getBaseOfPointer(ret->getReturnValue());
                                    toReturn.insert(interResult.begin(),interResult.end());
                                }
                            }
                        }
                    }
                }
            }
            DEBUG_PRINT("Done finding pointers for " << *pointer << "\n");
            return getBaseOfPointerDynamic[pointer]=toReturn;
        }
        
        void trackDerivedValues(Value * startingPoint) {
            if (threadDependantValues.count(startingPoint) != 0) {
                DEBUG_PRINT("Stopped coloring at " << *startingPoint << " because it has already been colored\n");
                return;
            }
            DEBUG_PRINT("Coloring " << *startingPoint << "\n");
            threadDependantValues.insert(startingPoint);
            for (auto use = startingPoint->users().begin();
                 use != startingPoint->users().end();
                 ++use) {                
                DEBUG_PRINT("Is used by: " << **use << "\n");
                Instruction *inst = dyn_cast<Instruction>(*use);
                if (inst && isCallSite(inst)) {
                    CallSite call = CallSite(inst);
                    DEBUG_PRINT("Was a function call, coloring corresponding arguments in function call...\n");
                    SmallPtrSet<Function*,1> calledFuns = getCalledFuns(inst);
                    for (Function * fun : calledFuns) {
                        DEBUG_PRINT("Coloring corresponding arguments of " << fun->getName() << " \n");
                        for (int opnum = 0; opnum < call.getNumArgOperands(); ++opnum) {
                            Value* callArg = call.getArgOperand(opnum);
                            if (callArg == startingPoint) {
                                //It's pretty stupid that we have to do this
                                for (Argument &arg : fun->getArgumentList())
                                    if (arg.getArgNo() == opnum)
                                        trackDerivedValues(&arg);
                            }
                        }
                        DEBUG_PRINT("Done coloring arguments for " << fun->getName() << " \n");
                    }
                } else if (auto store = dyn_cast<StoreInst>(*use)) {
                    DEBUG_PRINT("Was a store inst, coloring the root of the pointer operand\n");
                    SmallPtrSet<Value*,1> rootPointers = getBaseOfPointer(store->getPointerOperand());
                    for (Value * val : rootPointers)
                        trackDerivedValues(val);
                } else {
                    DEBUG_PRINT("Plainly coloring it\n");
                    trackDerivedValues(*use);
                }
                DEBUG_PRINT("Done coloring " << **use << "\n");
            }
        }
        
    };
}



char ThreadDependence::ID = 0;
static RegisterPass<ThreadDependence> V("thread-dependence",
                                        "Determines the values that might depend on thread arguments",
                                        true,
                                        true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
