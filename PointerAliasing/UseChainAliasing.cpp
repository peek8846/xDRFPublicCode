#ifndef _USECHAINALIASING_
#define _USECHAINALIASING_
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include <list>

#include "../ThreadDependantAnalysis/ThreadDependence.cpp"

// // #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

#define LIBRARYNAME "UseChainAliasing(class)"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << LIBRARYNAME << ": "
#define PRINT_DEBUG PRINTSTREAM << LIBRARYNAME << " (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE(LIBRARYNAME"-debug",PRINT_DEBUG << X)


//bool AssumeDGEPAliasConstBase = true;
static cl::opt<bool> AssumeDGEPAliasConstBase("no-dgep-alias-constbase",cl::desc("Do not resolve dynamic GEP offsets to their base in recursive SCEVs"));

//bool AssumeDependantIndexesDontAlias = true;
static cl::opt<bool> AssumeDependantIndexesDontAlias("no-dependant-index-noalias",cl::desc("Do not assume that GEP indices which depend on thread arguments make GEPs safe"),cl::init(true));

//bool AssumeDGEPNoAlias = false;
static cl::opt<bool> AssumeDGEPNoAlias("degep-noalias",cl::desc("Assume that GEP indices which are dynamic make GEPs safe"),cl::init(true));

Module *usechain_wm;
Pass *callingPass;

// DEPRECATED
// //Gets the called function of a callsite irregardless of casts
// Function *getStripCall(CallSite *callsite) {
//   Value *toReturn = callsite->getCalledValue()->stripPointerCasts();
//   return dyn_cast<Function>(toReturn);               
// }

//Verifies that a CallSite is not null-initialized
bool isNotNull(CallSite call) {
  return call.isCall() || call.isInvoke();
}

//Verifies that an instruction can be a callsite
bool isCallSite(Instruction* inst) {
  return isNotNull(CallSite(inst));
}

//Utility: Returns the proper type of a pointer type
Type *getTypeOfPointerType(Type *ptr) {
  while (PointerType *p = dyn_cast<PointerType>(ptr))
    ptr = p->getElementType();
  return ptr;
}

//Obtains the set of functions that can be immediately called when
//executing inst
SmallPtrSet<Function*,1> getCalledFuns(Instruction *inst) {
  //LIGHT_PRINT("Finding functions that can be called by " << *inst << "\n");
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
      if (auto fun = dyn_cast<Function>(nextValue)) {
	//LIGHT_PRINT(fun->getName() << " could be called\n");
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
      //Return a dummy "Null" value
      else if (auto inlineasm = dyn_cast<InlineAsm>(nextValue)) {
      	//LIGHT_PRINT("Could call assembly\n");
	toReturn.insert(NULL);
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


//Attempts to resolve a value to an integer using scalar evolution
//Is only more powerfull than constant folding in loops, where it will
//reduce an iterative variable to its base value
bool isBaseConstantInLoopSCEV(Value *val, ConstantInt **base, Function *containingFun) {
  DEBUG_PRINT("Simplifying " << *val << " using SCEV analysis\n");
  ScalarEvolution &SE = callingPass->getAnalysis<ScalarEvolutionWrapperPass>(*containingFun).getSE();
  const SCEV* scev_val = SE.getSCEV(val);
  // errs() << "Resolving SCEV for val: " << *val << " - ";
  // scev_val->print(errs());
  // errs() << "\n";
  while (!isa<SCEVConstant>(scev_val)) {
    if (auto scev_rec = dyn_cast<SCEVAddRecExpr>(scev_val)) {
      scev_val = scev_rec->getStart();
      continue;
    }
    // errs() << "Resolution failed, stopped at: ";
    // scev_val->print(errs());
    // errs() << "\n";
    DEBUG_PRINT("Failed, remaining SCEV was: " << *scev_val << "\n");
    return false;
  }
  *base = dyn_cast<SCEVConstant>(scev_val)->getValue();
            
  // if (scev_val != SE->getSCEV(val)) {
  //     errs() << "Resolved non-constant to: " << **base << "\n";
  // }
  DEBUG_PRINT("Sucessfully reduced to " << **base << "\n");
  return true;
  //return false;
}


//Returns whether any index of the dynamic gep depends on a thread argument
bool gepDependsOnThreadArgument(Value *GEP) {
  DEBUG_PRINT("Checking whether indices to " << *GEP << " could depend on thread arguments\n");
  ThreadDependence &TD = callingPass->getAnalysis<ThreadDependence>();
  for (auto it = dyn_cast<GetElementPtrInst>(GEP)->idx_begin(),
	 et = dyn_cast<GetElementPtrInst>(GEP)->idx_end();
       it != et; ++it) {
    if (TD.dependsOnThread(*it)) {
      DEBUG_PRINT(**it << " could depend on thread arguments\n");
      return true;
    }
  }
  DEBUG_PRINT("They could not\n");
  return false;
}


//Returns wether the dynamic gep was resolved
bool handleDynamicGEP(Value **pt_,APInt &offset) {
  //errs() << "!Detected dynamic use of GEP: " << **pt_ << ", #yolo-ing it\n";                    
  //Basically, we will try to get a constantExpr out of
  //the index and then manually recalculate our offset
  //and set the stripped value to it's pointer
  int offsetint = 0;
  Value *pt = *pt_;
  DEBUG_PRINT("Trying to resolve dynamic GEP " << *pt << "\n");
  Function *containingFun = dyn_cast<Function>(dyn_cast<Instruction>(*pt_)->getParent()->getParent());
  Type* nextType = dyn_cast<CompositeType>(dyn_cast<GetElementPtrInst>(pt)->getPointerOperand()->getType());

  for (auto it = dyn_cast<GetElementPtrInst>(pt)->idx_begin(),
	 et = dyn_cast<GetElementPtrInst>(pt)->idx_end();
       it != et; ++it) {
    DEBUG_PRINT("Resolving index: " << *it << "\n");
    assert(isa<CompositeType>(nextType) && "Broken Dynamic GEP detected");
    CompositeType *currType = cast<CompositeType>(nextType);
    ConstantInt *constant = NULL;

    bool isConstant = isBaseConstantInLoopSCEV(*it, &constant,containingFun);
    if (!isConstant) {
      DEBUG_PRINT("Was not constant when using SCEV\n");
      offsetint = -1;
      break;
    }
    int curroffset = constant->getZExtValue();
    nextType = currType->getTypeAtIndex(curroffset);

    // Handle a struct index, which adds its field offset to the pointer.
    if (StructType *STy = dyn_cast<StructType>(currType)) {
      const StructLayout *SL = usechain_wm->getDataLayout().getStructLayout(STy);
      offsetint += SL->getElementOffset(curroffset);
    } else {
      // For array or vector indices, scale the index by the size of the type.
      offsetint += curroffset *
	usechain_wm->getDataLayout().getTypeAllocSize(nextType);
    }
  }
  *pt_ = cast<GetElementPtrInst>(pt)->getPointerOperand();
  if (offsetint >= 0) {
    DEBUG_PRINT("Fully resolved dynamic GEP\n");
    //errs() << "Resolved Dynamic GEP" << "\n";
    offset += APInt(offset.getBitWidth(),offsetint);
    return true;
  } else {
    DEBUG_PRINT("Failed to resolve dynamic GEP\n");
    //offset += APInt(offset.getBitWidth(),0);
    return false;
    //errs() << "YOLO-ed Dynamic GEP" << "\n";
    //*pt_ = NULL;
  }
}

//Checks whether the address val might escape the local context
bool escapeCheck(Value *val) {
  DEBUG_PRINT("Checking whether memory reffered to by " << *val << " might escape context");
  if (!isa<PointerType>(val->getType())) {
    DEBUG_PRINT("Not a pointer, so false");
    return false;
  }
  if (isa<GlobalValue>(val)) {
    DEBUG_PRINT("Is a global, so true");
    return true;
  }
  bool toReturn = false;
  DEBUG_PRINT("Checking uses\n");
  for (Use &use : val->uses()) {
    Value * useval = use.get();
    if (auto store = dyn_cast<StoreInst>(useval))
      toReturn =  toReturn || escapeCheck(store->getPointerOperand());
    if (auto load = dyn_cast<LoadInst>(useval))
      toReturn = toReturn || false;
    if (Instruction* useinst = dyn_cast<Instruction>(useval)) {
      toReturn = toReturn || isCallSite(useinst);
    }
    toReturn = toReturn || escapeCheck(val);
  }
  DEBUG_PRINT("Determined to" << (toReturn ? "" : " not") << " escape\n");
  return toReturn;
}

SmallPtrSet<Value*,1024> visitedBottomLevelValues;
        
        
set<pair<Value*,list<int> > > findBottomLevelValues_(Value *val) {
  DEBUG_PRINT("Finding bottom level values of " << *val << "\n");
  int pointerSize = usechain_wm->getDataLayout().getPointerSizeInBits(cast<PointerType>(val->getType())->getAddressSpace());
  APInt offset = APInt(pointerSize,0);
  Value* strip = val->stripAndAccumulateInBoundsConstantOffsets(usechain_wm->getDataLayout(),offset);
  int intoffset = offset.getLimitedValue();
  set<pair<Value*,list<int> > > toReturn;
  bool appendOffset = true;
  SmallPtrSet<Value*,2> nextPointers;
  
  if (visitedBottomLevelValues.count(val) != 0)
    return toReturn;
  visitedBottomLevelValues.insert(val);
            
  //These are bottom level values, they modify toReturn directly
  //and do not add pointers to nextPointers
  if (auto inst = dyn_cast<Instruction>(strip)) {
    if (isCallSite(inst)) {
      DEBUG_PRINT("When stripped is callsite " << *inst << "\n");
      SmallPtrSet<Function*,1> calledFuns = getCalledFuns(inst);
      for (Function* fun : calledFuns) {
	//Inline asm case
	if (!fun) {
	  //Add parameters to nextPointers, scramble current list
	  intoffset = -1;
	  CallSite call(inst);
	  for (auto arg_beg = call.arg_begin();
	       arg_beg != call.arg_end(); ++arg_beg) {
	    nextPointers.insert(*arg_beg);
	  }
	}
	//Assume we know the names of all allocation functions
	if (fun->getName().equals("malloc") ||
	    fun->getName().equals("MyMalloc")) {
	  if (escapeCheck(strip)) {
	    toReturn.insert(make_pair((Value*)NULL,list<int>(1,intoffset)));
	    DEBUG_PRINT("Which is an escaped allocation: \n");
	  } else {
	    DEBUG_PRINT("Which is not an escaped allocation: \n");
	  }
	}
	else {
	  appendOffset=false;
	  //Find the return values of the function
	  for (auto instb = inst_begin(fun);
	       instb != inst_end(fun); ++instb) {
	    if (auto returninst = dyn_cast<ReturnInst>(&*instb)) {
	      if (Value* returnval = returninst->getReturnValue()) {
		DEBUG_PRINT("Added " << *(returnval) << " to nextpointers based on " << *inst << " has return " << *returninst << "\n");
		nextPointers.insert(returnval);
	      }
	    }
	  }
	}
      }
    }
  }
  if (auto glob = dyn_cast<GlobalVariable>(strip)) {
    DEBUG_PRINT("When stripped is global " << *glob << "\n");
      //errs() << "Stripped value is global\n";
    //errs() << "Found global: " << *glob << "\n";
    toReturn.insert(make_pair(glob,list<int>(1,intoffset)));
  }
  if (auto arg = dyn_cast<Argument>(strip)) {
    DEBUG_PRINT("When stripped is argument " << *arg << "\n");
    //errs() << "Stripped value is argument\n";
    //errs() << "Found argument: " << *arg << "\n";
    for (auto user : arg->getParent()->users()) {
      if (Instruction *inst = dyn_cast<Instruction>(user)) {
	if (isCallSite(inst)) {
	  CallSite call(inst);
	  appendOffset = false;
	  DEBUG_PRINT("Added " << *(call.getArgument(arg->getArgNo())) << " to nextpointers based on " << *inst << "\n");
	  nextPointers.insert(call.getArgument(arg->getArgNo()));
	}
      }
    }
    //toReturn.insert(make_pair((Value*)NULL,list<int>(1,intoffset)));
  }

  //These are the recursive cases, they add pointers to nextPointers
  //and define how to merge offsets
  if (auto load = dyn_cast<LoadInst>(strip)) {
    DEBUG_PRINT("When stripped is load " << *load << ", added pointer operand to nextpointers\n");
    nextPointers.insert(load->getPointerOperand());
  }
  if (auto dyngep = dyn_cast<GetElementPtrInst>(strip)) {
    DEBUG_PRINT("When stripped is dynamic gep " << *dyngep << ", added pointer operand to nextpointers\n");
    nextPointers.insert(dyngep->getPointerOperand());
    appendOffset = false;

    if (AssumeDependantIndexesDontAlias && gepDependsOnThreadArgument(dyngep)) {
      DEBUG_PRINT("Determined to vary based on thread arguments\n");
      intoffset = -2;
    } else if (AssumeDGEPAliasConstBase) {
      DEBUG_PRINT("Attempting to resolve dynamic GEP using SCEV\n");
      if (!handleDynamicGEP(&strip,offset)) {
	DEBUG_PRINT("Did not manage to resolve dynamic GEP\n");
	if (!AssumeDGEPNoAlias) {
	  DEBUG_PRINT("Conservatively set offset to dynamic\n");
	  intoffset = -1;
	} else {
	  DEBUG_PRINT("Optimistically discarded this comparison route\n");
	  nextPointers.erase(dyngep->getPointerOperand());
	}
      } else {
	DEBUG_PRINT("Resolved dynamic GEP to" << offset.getLimitedValue() << "\n");
	intoffset = offset.getLimitedValue();
      }
    } else {
      if (!AssumeDGEPNoAlias) {
	DEBUG_PRINT("Conservatively set offset to dynamic\n");
	intoffset = -1;
      } else {
	nextPointers.erase(dyngep->getPointerOperand());
	DEBUG_PRINT("Optimistically discarded this comparison route\n");
      }
    }
  }

  if (auto phi = dyn_cast<PHINode>(strip)) {
    DEBUG_PRINT("When stripped is phinode " << *phi << "\n");
    appendOffset = false;
    for (Use &use : cast<PHINode>(strip)->incoming_values()) {
      DEBUG_PRINT("Added " << *(use.get()) << " to nextpointers\n");
      nextPointers.insert(use.get());
    }
  }
    
#define UNIFY_OFFSETS(X,Y) ((X == -1 || Y == -1) ? -1 : X+Y)
    
  DEBUG_PRINT("Resolving nextpointers\n");
  
  for (Value* nextPoint : nextPointers) {
    DEBUG_PRINT("Resolving " << *nextPoint << "\n");
    set<pair<Value*,list<int> > > hasReturn = findBottomLevelValues_(nextPoint);
    for (set<pair<Value*,list<int> > >::iterator retPair = hasReturn.begin(),
	   end_retPair = hasReturn.end(); retPair != end_retPair; ++retPair) {
      list<int> newList = retPair->second;
      if (appendOffset)
	newList.push_back(intoffset);
      else {
	int oldlatest = newList.back();
	newList.pop_back();
	newList.push_back(UNIFY_OFFSETS(oldlatest,intoffset));
      }
      toReturn.insert(make_pair(retPair->first,newList));
    }
    DEBUG_PRINT("Done resolving " << *nextPoint << "\n");
  }
  DEBUG_PRINT("Done finding BLUs for " << *val << ", found " << toReturn.size() << " values\n");
#undef UNIFY_OFFSETS
  return toReturn;
}
 
 set<pair<Value*,list<int> > > findBottomLevelValues(Value *val) {
   visitedBottomLevelValues.clear();
   return findBottomLevelValues_(val);
 }
 
 map<pair<Value*,Value*>, AliasResult> pointerAliasDynamic;
 
 AliasResult pointerAlias(Value *pt1, Value *pt2, Pass *callingpass) {
  VERBOSE_PRINT("Comparing " << *pt1 << " and " << *pt2 << "\n");
  //errs() << "Usechainpointeralias is comparing " << *pt1 << " and " << *pt2 << "\n";
  if (pointerAliasDynamic.count(make_pair(pt1,pt2)) != 0) {
    VERBOSE_PRINT("Dynamically resolved to  " << pointerAliasDynamic[make_pair(pt1,pt2)] << "\n");
    //errs() << "Was previously resolved to " << (pointerAliasDynamic[make_pair(pt1,pt2)] ? "aliasing" : "not aliasing") << "\n"; 
    return pointerAliasDynamic[make_pair(pt1,pt2)];
  }

  callingPass = callingpass;
  
  set<pair<Value*,list<int> > > bottomUsesPt1 = findBottomLevelValues(pt1);
  set<pair<Value*,list<int> > > bottomUsesPt2 = findBottomLevelValues(pt2);

  //errs() << "pt1 bUses size: " << bottomUsesPt1.size() << "\n";
  //errs() << "pt2 bUses size: " << bottomUsesPt2.size() << "\n";
  
  LIGHT_PRINT(*pt1 << " bottomUserSize " << bottomUsesPt1.size() << "\n");
  LIGHT_PRINT(*pt2 << " bottomUserSize " << bottomUsesPt2.size() << "\n");
  
  AliasResult toReturn = NoAlias;

  for (set<pair<Value*,list<int> > >::iterator pt1pair = bottomUsesPt1.begin(),
	 end_pt1pair = bottomUsesPt1.end();
       pt1pair != end_pt1pair && !toReturn; ++pt1pair) {
    for (set<pair<Value*,list<int> > >::iterator pt2pair = bottomUsesPt2.begin(),
	   end_pt2pair = bottomUsesPt2.end();
	 pt2pair != end_pt2pair && !toReturn; ++pt2pair) {
      if (!pt1pair->first || !pt2pair->first) {
	//errs() << "At least one of the pointers got a NULL bottomLevelValue\n";
	LIGHT_PRINT("Skipped BLU comparison due to one of the BLUs having a null source\n");
	//toReturn = false;
	continue;
      }
      LIGHT_PRINT("Comparing BLUs: " << *(pt1pair->first) << " and " << *(pt2pair->first) << "\n");
      //errs() << "Comparing " << *(pt1pair->first) << " and " << *(pt2pair->first) << "\n";
      if (pt1pair->first != pt2pair->first) {
	LIGHT_PRINT("Did not alias, as the source pointers were different\n");
	continue;
      }
      auto pt1b = pt1pair->second.rbegin();
      auto pt2b = pt2pair->second.rbegin();
      bool listChecksOut = true;
      bool strictMatch = true;
      DEBUG_PRINT("Started comparisons of indexing lists\n");
      while (pt1b != pt1pair->second.rend() &&
	     pt2b != pt2pair->second.rend()) {
	DEBUG_PRINT("Comparing " << *pt1b << " and " << *pt2b << "\n");

	if (*pt1b == -2 || *pt2b == -2) {
	  DEBUG_PRINT("Atleast one of the indices were dynamic and depends on thread arguments. Optimistically the index lists are then different\n"); 
	  listChecksOut = false;
	  break;
	}
	
	if (*pt1b != -1 && *pt2b != -1 && *pt1b != *pt2b) {
	  DEBUG_PRINT("Indexes were different\n");
	  listChecksOut = false;
	  break;
	}
	if (*pt1b == -1 || *pt2b == -1) {
	  DEBUG_PRINT("Atleast one index was dynamic\n");
	  strictMatch = false;
	}
	pt1b++;
	pt2b++;
      }
      if (pt1b != pt1pair->second.rend() ||
	  pt2b != pt2pair->second.rend()) {
	LIGHT_PRINT("BLUs did not alias as their indexing lists were different\n");
	continue;
      }
      if (listChecksOut) {
	if (!strictMatch) {
	  LIGHT_PRINT("BLUs may alias\n");
	  if (toReturn != MustAlias)
	    toReturn = MayAlias;
	} else {
	  LIGHT_PRINT("BlUs must alias\n");
	  toReturn = MustAlias;
	}
      }
    }
  }
  
  VERBOSE_PRINT("Determined to " << toReturn << "\n");
  return pointerAliasDynamic[make_pair(pt1,pt2)]=toReturn;
}

SmallPtrSet<Value*,1024> visitedAliasValues;

// DEPRECATED
// //Pointer comparsion
// //Checks wether the pointer arguments to two instructions
// //do not alias
// bool pointerConflict(Instruction *P1, Instruction *P2, Module *M) {
//   usechain_wm = M;
//   SmallPtrSet<Value*,4> P1Pargs;
//   SmallPtrSet<Value*,4> P2Pargs;
//   if (auto P1_load = dyn_cast<LoadInst>(P1))
//     P1Pargs.insert(P1_load->getPointerOperand());
//   if (auto P1_store = dyn_cast<StoreInst>(P1))
//     P1Pargs.insert(P1_store->getPointerOperand());
//   if (auto P1_call = CallSite(P1))
//     for (Use &arg : P1_call.args())
//       if (isa<PointerType>(arg.get()->getType()))
// 	P1Pargs.insert(arg.get());
//   if (auto P2_load = dyn_cast<LoadInst>(P2))
//     P2Pargs.insert(P2_load->getPointerOperand());
//   if (auto P2_store = dyn_cast<StoreInst>(P2))
//                 P2Pargs.insert(P2_store->getPointerOperand());
//   if (auto P2_call = CallSite(P2))
//     for (Use &arg : P2_call.args())
//       if (isa<PointerType>(arg.get()->getType()))
// 	P2Pargs.insert(arg.get());
//   bool toReturn = false;
//   for (Value *P1a : P1Pargs) {
//     if (toReturn)
//       break;
//     if(isa<PointerType>(P1a->getType()))
//       for (Value *P2a : P2Pargs) {
// 	if (toReturn)
// 	  break;
// 	if (isa<PointerType>(P2a->getType()))
// 	  if (pointerAlias(P1a,P2a)) {
// 	    toReturn = true;
// 	  }
//       }
//   }
//   return toReturn;
// }

#endif
