#ifndef _ALIASCOMBINER_
#define _ALIASCOMBINER_
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/Module.h"

#include <list>

#include "UseChainAliasing.cpp"
// #include "WPA/FlowSensitive.h"
// #include "MemoryModel/PointerAnalysis.h"

#define LIBRARYNAME "AliasCombiner(class)"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << LIBRARYNAME << ": "
#define PRINT_DEBUG PRINTSTREAM << LIBRARYNAME << " (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE("light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

//Functions that should never be considered for tracking
set<StringRef> noAnalyzeFunctions = {"begin_NDRF","end_NDRF","begin_XDRF","end_XDRF"};

class AliasCombiner {
  
public:
    AliasCombiner(Module *mod, Pass *callingPass) {
        AliasCombiner(mod,false,callingPass);
    }

    AliasCombiner(Module *mod, bool useUseChain, Pass *callingPass) {
        // module=mod;
        // useUseChainAliasing=useUseChain;
        // this->callingPass=callingPass;
        AliasCombiner(mod, useUseChain, callingPass, MustAlias);
    }

    AliasCombiner(Module *mod, bool useUseChain, Pass *callingPass, AliasResult aliasLevel) {
        module=mod;
        useUseChainAliasing=useUseChain;
        willAliasLevel=aliasLevel;
        this->callingPass=callingPass;
        //flowSensitive=FlowSensitive::createFSWPA(*mod);
    }

    //If any alias analysis says they do not alias, this returns false. Otherwise returns true.
    //More specifically, if we can for each argument to the instruction find atleast one proof it does not alias
    //then we say it does not alias
    //Note, an "alias" in this sense means that the instructions could access the same data when ran by different threads
    bool MayConflict(Instruction *ptr1, Instruction *ptr2) {
        DEBUG_PRINT("Examining whether accesses " << *ptr1 << " and " << *ptr2 << " are not aliasing under any analysis\n");
        bool toReturn=false;
        SmallPtrSet<Value*,4> ptr1args=getArguments(ptr1);
        SmallPtrSet<Value*,4> ptr2args=getArguments(ptr2);
        for (Value *P1a : ptr1args) {
            if(isa<PointerType>(P1a->getType())) {
                for (Value *P2a : ptr2args) {
                    if (isa<PointerType>(P2a->getType())) {
                        DEBUG_PRINT("Determining whether " << *P1a << " and " << *P2a << " may optimistically conflict\n");
                            
                        if (!(canBeShared(P1a) && canBeShared(P2a))) {
                            DEBUG_PRINT("Determined at least one of them cannot be shared between threads\n");
                            continue;
                        }

                        if (useUseChainAliasing) {
                            DEBUG_PRINT("Testing with usechainaliasing\n");
                            usechain_wm=module;
                            if (pointerAlias(P1a,P2a) == false) {
                                DEBUG_PRINT("Determined to not alias by use chain analysis\n");
                                continue;
                            }
                            else
                                DEBUG_PRINT("Was not determined to not alias by usechainaliasing\n");
                        }
                        
                        pair<Value*,Value*> comparable=getComparableValues(P1a,P2a);
                        //pair<Value*,Value*> comparable=make_pair(P1a,P2a);
                        if (!(comparable.first && comparable.second)) {
                            DEBUG_PRINT("Failed to find comparable values\n");
                            continue;
                        }
                        
                        Function * parent = NULL;
                        if (Instruction * inst = dyn_cast<Instruction>(comparable.first)) {
                            parent=inst->getParent()->getParent() ? inst->getParent()->getParent() : parent;
                        }
                        if (Argument * inst = dyn_cast<Argument>(comparable.first)) {
                            parent=inst->getParent() ? inst->getParent() : parent;
                        }
                        if (Instruction * inst = dyn_cast<Instruction>(comparable.second)) {
                            parent=inst->getParent()->getParent() ? inst->getParent()->getParent() : parent;
                        }
                        if (Argument * inst = dyn_cast<Argument>(comparable.second)) {
                            parent=inst->getParent() ? inst->getParent() : parent;
                        }
                        
                        LIGHT_PRINT("Comparing " << *(comparable.first) << " and " << *(comparable.second) << "\n");
                        LIGHT_PRINT("Which have types: " << typeid(*comparable.first).name() << " and " << typeid(*comparable.second).name() << "\n");

                        //Some shortcutting is desirable here
                        if (isa<GlobalVariable>(comparable.first) && isa<GlobalVariable>(comparable.second)) {
                            //Might want to do more advanced stuff later
                            if (comparable.first == comparable.second) {
                                DEBUG_PRINT("Determined to alias by virtue of being the same global");
                                return true;
                            }
                        }
                        
                        //This is for the weird case where no comparable value is within a function.
                        if (!parent) {
                            DEBUG_PRINT("Neither comparable value is within a function\n");
                            continue;
                        }

                        bool aliased=false;
                        //for (Pass *aa : aliasResults) {
                            //bool aliased=false;
                        AliasResult res = getAAResultsForFun(parent)->alias(comparable.first,comparable.second);
                        switch (res) {
                            DEBUG_PRINT("Got NoAlias\n");
                            if (willAliasLevel > NoAlias) {
                                break;
                            }
                        case MayAlias:
                            DEBUG_PRINT("Got MayAlias\n");
                            if (willAliasLevel > MayAlias) {
                                break;
                            }
                        case PartialAlias:
                            DEBUG_PRINT("Got PartialAlias\n");
                            if (willAliasLevel > PartialAlias) {
                                break;
                            }
                        case MustAlias:
                            DEBUG_PRINT("Got MustAlias\n");
                        default:
                            aliased=true;
                            break;
                        }
                        if (!aliased) {
                            LIGHT_PRINT("Determined they did not alias\n");
                            continue;
                        } else {
                            LIGHT_PRINT("Determined that they aliased\n");
                            return true;
                        }
                    }
                }
            }
        }
        DEBUG_PRINT("Returned " << (toReturn ? "true\n" : "false\n"));
        return toReturn;
    }

    // bool MustConflict(Instruction *ptr1, Instruction *ptr2) {
    //     return MayConflict(ptr1,ptr2);
    // }

    //If any alias analysis says they must alias, this returns true. Otherwise returns false
    //more specifically, for each argument we need to prove it does not alias, and if we can then we return false
    bool MustConflict(Instruction *ptr1, Instruction *ptr2) {
        DEBUG_PRINT("Examining whether accesses " << *ptr1 << " and " << *ptr2 << " are aliasing under any analysis\n");
        bool toReturn=false;
        SmallPtrSet<Value*,4> ptr1args=getArguments(ptr1);
        SmallPtrSet<Value*,4> ptr2args=getArguments(ptr2);
        for (Value *P1a : ptr1args) {
            if(isa<PointerType>(P1a->getType())) {
                for (Value *P2a : ptr2args) {
                    if (isa<PointerType>(P2a->getType())) {
                        DEBUG_PRINT("Determining whether " << *P1a << " and " << *P2a << " may conservatively conflict\n");

                        if (!(canBeShared(P1a) && canBeShared(P2a))) {
                            DEBUG_PRINT("Determined at least one of them cannot be shared between threads\n");
                            continue;
                        }

                        if (useUseChainAliasing) {
                            DEBUG_PRINT("Testing with usechainaliasing\n");
                            usechain_wm=module;
                            if (pointerAlias(P1a,P2a) == true) {
                                DEBUG_PRINT("Determined to alias by usechainaliasing\n");
                                toReturn=true;
                            }
                            else
                                DEBUG_PRINT("Was not determined to alias by usechainaliasing\n");
                        }
                        pair<Value*,Value*> comparable=getComparableValues(P1a,P2a);
                        if (!(comparable.first && comparable.second)) {
                            DEBUG_PRINT("Failed to find comparable values\n");
                            continue;
                        }

                        Function * parent = NULL;
                        if (Instruction * inst = dyn_cast<Instruction>(comparable.first)) {
                            parent=inst->getParent()->getParent() ? inst->getParent()->getParent() : parent;
                        }
                        if (Argument * inst = dyn_cast<Argument>(comparable.first)) {
                            parent=inst->getParent() ? inst->getParent() : parent;
                        }
                        if (Instruction * inst = dyn_cast<Instruction>(comparable.second)) {
                            parent=inst->getParent()->getParent() ? inst->getParent()->getParent() : parent;
                        }
                        if (Argument * inst = dyn_cast<Argument>(comparable.second)) {
                            parent=inst->getParent() ? inst->getParent() : parent;
                        }

                        LIGHT_PRINT("Comparing " << *(comparable.first) << " and " << *(comparable.second) << "\n");
                        LIGHT_PRINT("Which have types: " << typeid(*comparable.first).name() << " and " << typeid(*comparable.second).name() << "\n");

                        //Some shortcutting is desirable here
                        if (isa<GlobalVariable>(comparable.first) && isa<GlobalVariable>(comparable.second)) {
                            //Might want to do more advanced stuff later
                            if (comparable.first == comparable.second) {
                                DEBUG_PRINT("Determined to alias by virtue of being the same global");
                                return true;
                            }
                        }
                        
                        //This is for the weird case where no comparable value is within a function.
                        if (!parent) {
                            DEBUG_PRINT("Neither comparable value is within a function\n");
                            continue;
                        }
                        
                        bool aliased=false;
                        //for (Pass *aa : aliasResults) {
                        
                        AliasResult res = getAAResultsForFun(parent)->alias(comparable.first,comparable.second);
                        switch (res) {
                        case NoAlias:
                            DEBUG_PRINT("Got NoAlias\n");
                            if (willAliasLevel > NoAlias) {
                                break;
                            }
                        case MayAlias:
                            DEBUG_PRINT("Got MayAlias\n");
                            if (willAliasLevel > MayAlias) {
                                break;
                            }
                        case PartialAlias:
                            DEBUG_PRINT("Got PartialAlias\n");
                            if (willAliasLevel > PartialAlias) {
                                break;
                            }
                        case MustAlias:
                            DEBUG_PRINT("Got MustAlias\n");
                        default:
                            aliased=true;
                            break;
                        }
                        if (aliased) {
                            DEBUG_PRINT("Determined to alias by LLVM alias analysis\n");
                            return true;
                        }
                        else
                            DEBUG_PRINT("Did not find any proof of aliasing\n");
                    }
                }
            }
        }
        return toReturn;
    }

    // void addAliasResult(Pass *result) {
    //     aliasResults.push_back(result);
    // }

private:

    Module *module;
    Pass *callingPass;

    // FlowSensitive *flowSensitive;

    // list<Pass*> aliasResults;
    map<Function*,AAResults*> AAResultMap;

    map<pair<Instruction*,Instruction*>,bool> shortcutConservative;
    map<pair<Instruction*,Instruction*>,bool> shortcutOptimistic;

    AAResults * getAAResultsForFun(Function* parent) {
        if (AAResultMap.count(parent) != 0) {
            return AAResultMap[parent];
        }
        BasicAAResult * newbase = new BasicAAResult(createLegacyPMBasicAAResult(*callingPass,*parent));
        AAResults *newaares = new AAResults(createLegacyPMAAResults(*callingPass,*parent,*newbase));
        //*newaares=createLegacyPMAAResults(*callingPass,*parent,base);
        return AAResultMap[parent]=newaares;
    }
                                     

    bool useUseChainAliasing;

    AliasResult willAliasLevel=MustAlias;

    pair<Value*,Value*> getComparableValues(Value *val1, Value* val2) {
        bool foundGlobalForVal1=false;
        bool foundGlobalForVal2=false;
        
        SmallPtrSet<Value*,4> compareTowards1;
        SmallPtrSet<Value*,4> compareTowards2;
        SmallPtrSet<Value*,4> expandNext1;
        SmallPtrSet<Value*,4> expandNext2;
        expandNext1.insert(val1);
        expandNext2.insert(val2);
        while (expandNext1.size() != 0 || expandNext2.size() != 0) {
            DEBUG_PRINT("Expanding next, sizes are: " << expandNext1.size() << " x " << expandNext2.size() << " (" << compareTowards1.size() << ", " << compareTowards2.size() << ")\n");
            DEBUG_PRINT("Sets are:\n");
            DEBUG_PRINT("EN1:\n");
            for (Value * val : expandNext1)
                DEBUG_PRINT(*val << "\n");
            DEBUG_PRINT("EN2:\n");
            for (Value * val : expandNext2)
                DEBUG_PRINT(*val << "\n");
            DEBUG_PRINT("CT1:\n");
            for (Value * val : compareTowards1)
                DEBUG_PRINT(*val << "\n");
            DEBUG_PRINT("CT2:\n");
            for (Value * val : compareTowards2)
                DEBUG_PRINT(*val << "\n");
            for (Value* val1_e : expandNext1) {
                Function *parent1=NULL;
                if (Instruction *val1_i = dyn_cast<Instruction>(val1_e))
                    parent1=val1_i->getParent()->getParent();
                if (Argument *val1_a = dyn_cast<Argument>(val1_e))
                    parent1=val1_a->getParent();
                for (Value* val2_c : compareTowards2) {
                    if (isa<GlobalValue>(val1_e) || isa<GlobalValue>(val2_c))
                        if (!(isa<GlobalValue>(val1_e) && isa<GlobalValue>(val2_c)))
                            return make_pair(val1_e,val2_c);
                    Function *parent2=NULL;
                    if (Instruction *val2_i = dyn_cast<Instruction>(val2_c))
                        parent2=val2_i->getParent()->getParent();
                    if (Argument *val2_a = dyn_cast<Argument>(val2_c))
                        parent2=val2_a->getParent();
                    if (parent1==parent2)
                        return make_pair(val1_e,val2_c);
                }
                for (Value* val2_e : expandNext2) {
                    if (isa<GlobalValue>(val1_e) || isa<GlobalValue>(val2_e))
                        if (!(isa<GlobalValue>(val1_e) && isa<GlobalValue>(val2_e)))
                            return make_pair(val1_e,val2_e);
                    Function *parent2=NULL;
                    if (Instruction *val2_i = dyn_cast<Instruction>(val2_e))
                        parent2=val2_i->getParent()->getParent();
                    if (Argument *val2_a = dyn_cast<Argument>(val2_e))
                        parent2=val2_a->getParent();
                    if (parent1==parent2)
                        return make_pair(val1_e,val2_e);
                }
            }
      
            for (Value* val2_e : expandNext2) {
                Function *parent2=NULL;
                if (Instruction *val2_i = dyn_cast<Instruction>(val2_e))
                    parent2=val2_i->getParent()->getParent();
                if (Argument *val2_a = dyn_cast<Argument>(val2_e))
                    parent2=val2_a->getParent();
                for (Value* val1_c : compareTowards1) {
                    if (isa<GlobalValue>(val1_c) || isa<GlobalValue>(val2_e))
                        if (!(isa<GlobalValue>(val1_c) && isa<GlobalValue>(val2_e)))
                            return make_pair(val1_c,val2_e);
                    Function *parent1=NULL;
                    if (Instruction *val1_i = dyn_cast<Instruction>(val1_c))
                        parent2=val1_i->getParent()->getParent();
                    if (Argument *val1_a = dyn_cast<Argument>(val1_c))
                        parent2=val1_a->getParent();
                    if (parent1==parent2)
                        return make_pair(val1_c,val2_e);
                }
            }	
    
            for (Value* val1_e : expandNext1) {
                compareTowards1.insert(val1_e);
            }
            for (Value* val2_e : expandNext2) {
                compareTowards2.insert(val2_e);
            }
      
            //At this point, none of the previous values have been in the same function. So we must expand them
            SmallPtrSet<Value*,4> expandNext1_new;
            for (Value * val1_e : expandNext1) {
                val1_e = val1_e->stripPointerCasts();
                bool canGetOutsideContext=false;
                SmallPtrSet<Value*,2> oContext;
                if (auto val1_i = dyn_cast<Instruction>(val1_e)) {
                    SmallPtrSet<Value*,2> oContext = getAliasedValuesOutsideContext(val1_i,foundGlobalForVal1);
                    canGetOutsideContext=true;
                }
                if (auto val1_a = dyn_cast<Argument>(val1_e)) {
                    SmallPtrSet<Value*,2> oContext = getAliasedValuesOutsideContext(val1_a);
                    canGetOutsideContext=true;
                }
                if (canGetOutsideContext) {
                    for (Value * val1_oc : oContext) {
                        val1_oc = val1_oc->stripPointerCasts();
                        if (compareTowards1.count(val1_oc))
                            expandNext1_new.insert(val1_oc);
                    }
                }
            }
            expandNext1=expandNext1_new;
            SmallPtrSet<Value*,4> expandNext2_new;
            for (Value * val2_e : expandNext2) {
                val2_e = val2_e->stripPointerCasts();
                bool canGetOutsideContext=false;
                SmallPtrSet<Value*,2> oContext;
                if (auto val2_i = dyn_cast<Instruction>(val2_e)) {	
                    SmallPtrSet<Value*,2> oContext = getAliasedValuesOutsideContext(val2_i,foundGlobalForVal2);
                    canGetOutsideContext=true;
                }
                if (auto val2_a = dyn_cast<Argument>(val2_e)) {	
                    SmallPtrSet<Value*,2> oContext = getAliasedValuesOutsideContext(val2_a);
                    canGetOutsideContext=true;
                }
                if (canGetOutsideContext) {
                    for (Value * val2_oc : oContext) {
                        val2_oc = val2_oc->stripPointerCasts();
                        if (compareTowards2.count(val2_oc) == 0)
                            expandNext2_new.insert(val2_oc);
                    }
                }
            }
            expandNext2=expandNext2_new;
        }
        return make_pair((Value*)NULL,(Value*)NULL);
    }
  
    bool mayConflictSameContext(Instruction *ptr1, Value* ptr2) {
        //DEBUG_PRINT("Checking whether " << *ptr1 << " and " << *ptr2 << " might alias in the same context\n");
        // if (useUseChainAliasing) {
        //     DEBUG_PRINT("Testing with usechainaliasing\n");
        //     usechain_wm=module;
        //     bool toReturn=pointerAlias(ptr1,ptr2);
        //     if (toReturn) {
        //         DEBUG_PRINT("They did\n");    
        //     } else {
        //         DEBUG_PRINT("They did not\n");    
        //     }
        //     return toReturn;
        // } else {
        bool toReturn=true;
        //for (Pass *results : aliasResults) {
        bool aliased=false;
        Function * parent = dyn_cast<Instruction>(ptr1)->getFunction();
        DEBUG_PRINT("Done calling alias\n");
        DEBUG_PRINT(*ptr1 << "\n");
        AliasResult res = getAAResultsForFun(parent)->alias(ptr1,ptr2); 
        switch (res) {
        case NoAlias:
            //                    if (willAliasLevel > NoAlias) {
            break;
            //}
        case MayAlias:
            //if (willAliasLevel > MayAlias) {
            //break;
            //}
        case PartialAlias:
            // if (willAliasLevel > PartialAlias) {
            //     break;
            // }
        case MustAlias:
        default:
            aliased=true;
            break;
        }
        DEBUG_PRINT("Done with switch...\n");
        if (!aliased) {
            toReturn=false;
        }
        //}
        if (toReturn) {
            DEBUG_PRINT("They did\n");    
        } else {
            DEBUG_PRINT("They did not\n");    
        }
        return toReturn;
        //}
    }

    SmallPtrSet<Value*,2> getAliasedValuesOutsideContext(Argument *arg) {
        SmallPtrSet<Value*,2> toReturn;
        for (auto user : arg->getParent()->users()) {
            if (Instruction *inst = dyn_cast<Instruction>(user)) {
                if (isCallSite(inst)) {
                    CallSite call(inst);
                    toReturn.insert(call.getArgument(arg->getArgNo()));
                }
            }
        }
        return toReturn;
    }

    SmallPtrSet<Value*,2> getAliasedValuesOutsideContext(GlobalValue *glob) {
        SmallPtrSet<Value*,2> toReturn;
        // for (auto user : arg->getParent()->users()) {
        //     if (Instruction *inst = dyn_cast<Instruction>(user)) {
        //         if (isCallSite(inst)) {
        //             CallSite call(inst);
        //             toReturn.insert(call.getArgument(arg->getArgNo()));
        //         }
        //     }
        // }
        toReturn.insert(glob);
        return toReturn;
    }

    SmallPtrSet<Value*,2> getAliasedValuesOutsideContext(Instruction *val,bool &comparetoglobsalready) {
        SmallPtrSet<Value*,2> toReturn;
        for (Argument &arg : val->getParent()->getParent()->getArgumentList()) {
            if (isa<PointerType>(arg.getType()) && mayConflictSameContext(val,&arg)) {
                for (auto user : val->getParent()->getParent()->users()) {
                    if (Instruction *inst = dyn_cast<Instruction>(user)) {
                        if (isCallSite(inst)) {
                            CallSite call(inst);
                            toReturn.insert(call.getArgument(arg.getArgNo()));
                        }
                    }
                }
            }
        }
        if (comparetoglobsalready) {
            for (GlobalValue &glob : module->getGlobalList()) {
                if (isa<PointerType>(glob.getType()) && mayConflictSameContext(val,&glob)) {
                    toReturn.insert(&glob);
                    comparetoglobsalready=true;
                }
            }
        }
        return toReturn;
    }
  
    //Utility: Checks wether a given callsite contains a call
    bool isNotNull(CallSite call) {
        return call.isCall() || call.isInvoke();
    }
  
    //Utility: Checks whether an instruction could be a callsite
    bool isCallSite(Instruction* inst) {
        return isNotNull(CallSite(inst));
    }
    
    //Utility: Returns the proper type of a pointer type
    Type *getTypeOfPointerType(Type *ptr) {
        while (PointerType *p = dyn_cast<PointerType>(ptr))
            ptr = p->getElementType();
        return ptr;
    }

    SmallPtrSet<Function*,1> getCalledFuns(Instruction *inst) {
        SmallPtrSet<Function*,1> toReturn;
        SmallPtrSet<Value*,8> alreadyVisited;
        if (isCallSite(inst)) {
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
                
                //Here we pick apart data structures
                else if (auto gep = dyn_cast<GetElementPtrInst>(nextValue)) {
                    //Any remaining gep must, by definition, have a dynamic index
                    //So we just resolve the value that is gepped from
                    calledValues.push_back(gep->getPointerOperand());
                }
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
                    for (Function &fun : inst->getParent()->getParent()->getParent()->getFunctionList()) {
                        if (fun.hasAddressTaken()) {
                            if (fun.getFunctionType() == dyn_cast<FunctionType>(getTypeOfPointerType(glob->getType()))) {
                                toReturn.insert(&fun);
                            }
                        }
                    }
                } else {
                    //We failed to resolve function to be called. Print diagnostic message
                    // VERBOSE_PRINT("Failed to resolve value: " << *nextValue
                    //               << "\nwhich has type: " << typeid(*nextValue).name()
                    //               << "\nwhile resolving called functions.\n");
                }                    
            }
        }
        return toReturn;
    }
    
    bool escapeCheck(Value *val) {
        if (!isa<PointerType>(val->getType()))
            return false;
        if (isa<GlobalValue>(val))
            return true;
        bool toReturn = false;
        for (Use &use : val->uses()) {
            Value * useval = use.get();
            if (auto store = dyn_cast<StoreInst>(useval))
                toReturn =  toReturn || escapeCheck(store->getPointerOperand());
            if (auto load = dyn_cast<LoadInst>(useval))
                toReturn = toReturn || false;
            if (Instruction* useinst = dyn_cast<Instruction>(useval))
                toReturn = toReturn || isCallSite(useinst);
            toReturn = toReturn || escapeCheck(val);
        }
        return toReturn;
    }

    map<Value*,bool> canBeSharedDynamic;
    bool canBeShared(Value *val) {
        if (canBeSharedDynamic.count(val) != 0) {
            return canBeSharedDynamic[val];
        }
        DEBUG_PRINT("Determining whether " << *val << " can be shared...\n");
        //This ensures that recursion does not break us
        canBeSharedDynamic[val]=false;
        
        if (auto inst = dyn_cast<Instruction>(val)) {

            SmallPtrSet<Function*,1> calledFuns=getCalledFuns(inst);
            if (calledFuns.size() != 0)
                DEBUG_PRINT("Is a call\n");
            for (Function * calledFun : calledFuns) {
                if (calledFun->getName().equals("malloc") ||
                    calledFun->getName().equals("MyMalloc")
                    ) {
                    DEBUG_PRINT("Called malloc variant\n");
                    if (escapeCheck(val)) {
                        DEBUG_PRINT("Allocation escapes\n");
                        return canBeSharedDynamic[val]=true;
                    }
                }
                else {
                    for (auto it = inst_begin(calledFun);
                         it != inst_end(calledFun); ++it) {
                        if (auto ret = dyn_cast<ReturnInst>(&*it))
                            if (ret->getReturnValue() && canBeShared(ret->getReturnValue()))
                                return canBeSharedDynamic[val]=true;
                    }
                }
            }
        }
        if (auto glob = dyn_cast<GlobalVariable>(val)) {
            return canBeSharedDynamic[val]=true;
        }
        if (auto arg = dyn_cast<Argument>(val)) {
            if (arg->getParent()->hasAddressTaken())
                return canBeSharedDynamic[val]=true;
            for (auto user : arg->getParent()->users()) {
                if (Instruction *inst = dyn_cast<Instruction>(user)) {
                    if (isCallSite(inst)) {
                        CallSite call(inst);
                        if (canBeShared(call.getArgument(arg->getArgNo())))
                            return canBeSharedDynamic[val]=true;
                    }
                }
            }
        }
        
        if (auto load = dyn_cast<LoadInst>(val)) {
            return canBeSharedDynamic[val]=canBeShared(load->getPointerOperand());
        }
        if (auto store = dyn_cast<StoreInst>(val)) {
            return canBeSharedDynamic[val]=canBeShared(store->getPointerOperand());
        }
        if (auto gep = dyn_cast<GetElementPtrInst>(val)) {
            return canBeSharedDynamic[val]=canBeShared(gep->getPointerOperand());
        }
        if (auto phi = dyn_cast<PHINode>(val)) {
            for (Use &use : cast<PHINode>(val)->incoming_values())
                return canBeSharedDynamic[val]=canBeShared(use.get());
        }

        if (val->stripPointerCasts() != val)
            if (canBeShared(val->stripPointerCasts()))
                return canBeSharedDynamic[val]=true;

        DEBUG_PRINT("Handling of " << *val << " fell through\n");
        return canBeSharedDynamic[val]=false;
    }

    SmallPtrSet<Value*,4> getArguments(Instruction *inst) {
        SmallPtrSet<Value*,4> args;
        if (auto inst_load = dyn_cast<LoadInst>(inst))
            args.insert(inst_load->getPointerOperand());
        if (auto inst_store = dyn_cast<StoreInst>(inst))
            args.insert(inst_store->getPointerOperand());
        if (auto inst_call = CallSite(inst))
            for (Use &arg : inst_call.args())
                if (isa<PointerType>(arg.get()->getType()))
                    args.insert(arg.get());
        return args;
    }
};
    
#endif

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
