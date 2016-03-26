#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/CallSite.h"
#include <list>

// // #include "llvm/Analysis/ScalarEvolution.h"
// #include "llvm/Analysis/ScalarEvolutionExpressions.h"

bool AssumeDGEPAliasConstBase = true;
bool AssumeDGEPNoAlias = true;

Module *wM;

//Gets the called function of a callsite irregardless of casts
Function *getStripCall(CallSite *callsite) {
  Value *toReturn = callsite->getCalledValue()->stripPointerCasts();
  return dyn_cast<Function>(toReturn);               
}

//Verifies that a CallSite is not null-initialized
bool isNotNull(CallSite call) {
  return call.isCall() || call.isInvoke();
}

//Verifies that an instruction can be a callsite
bool isCallSite(Instruction* inst) {
  return isNotNull(CallSite(inst));
}

//Attempts to resolve a value to an integer using scalar evolution
//Is only more powerfull than constant folding in loops, where it will
//reduce an iterative variable to its base value
bool isBaseConstantInLoopSCEV(Value *val, ConstantInt **base, Function *containingFun) {
  // ScalarEvolution *SE = getSE(containingFun);
  // const SCEV* scev_val = SE->getSCEV(val);
  // // errs() << "Resolving SCEV for val: " << *val << " - ";
  // // scev_val->print(errs());
  // // errs() << "\n";
  // while (!isa<SCEVConstant>(scev_val)) {
  //   if (auto scev_rec = dyn_cast<SCEVAddRecExpr>(scev_val)) {
  //     scev_val = scev_rec->getStart();
  //     continue;
  //   }
  //   // errs() << "Resolution failed, stopped at: ";
  //   // scev_val->print(errs());
  //   // errs() << "\n";
  //   return false;
  // }
  // *base = dyn_cast<SCEVConstant>(scev_val)->getValue();
            
  // // if (scev_val != SE->getSCEV(val)) {
  // //     errs() << "Resolved non-constant to: " << **base << "\n";
  // // }
  // return true;
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
  Function *containingFun = dyn_cast<Function>(dyn_cast<Instruction>(*pt_)->getParent()->getParent());
  Type* nextType = dyn_cast<CompositeType>(dyn_cast<GetElementPtrInst>(pt)->getPointerOperand()->getType());
  for (auto it = dyn_cast<GetElementPtrInst>(pt)->idx_begin(),
	 et = dyn_cast<GetElementPtrInst>(pt)->idx_end();
       it != et; ++it) {
    assert(isa<CompositeType>(nextType) && "Broken Dynamic GEP detected");
    CompositeType *currType = cast<CompositeType>(nextType);
    ConstantInt *constant = NULL;
    bool isConstant = isBaseConstantInLoopSCEV(*it, &constant,containingFun);
    if (!isConstant) {
      offsetint = -1;
      break;
    }
    int curroffset = constant->getZExtValue();
    nextType = currType->getTypeAtIndex(curroffset);

    // Handle a struct index, which adds its field offset to the pointer.
    if (StructType *STy = dyn_cast<StructType>(currType)) {
      const StructLayout *SL = wM->getDataLayout().getStructLayout(STy);
      offsetint += SL->getElementOffset(curroffset);
    } else {
      // For array or vector indices, scale the index by the size of the type.
      offsetint += curroffset *
	wM->getDataLayout().getTypeAllocSize(nextType);
    }
  }
  *pt_ = cast<GetElementPtrInst>(pt)->getPointerOperand();
  if (offsetint >= 0) {
    //errs() << "Resolved Dynamic GEP" << "\n";
    offset += APInt(offset.getBitWidth(),offsetint);
    return true;
  } else {
    //offset += APInt(offset.getBitWidth(),0);
    return false;
    //errs() << "YOLO-ed Dynamic GEP" << "\n";
    //*pt_ = NULL;
  }
}

//Checks whether the address val might escape the local context
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

SmallPtrSet<Value*,1024> visitedBottomLevelValues;
        
        
set<pair<Value*,list<int> > > findBottomLevelValues_(Value *val) {
  int pointerSize = wM->getDataLayout().getPointerSizeInBits(cast<PointerType>(val->getType())->getAddressSpace());
  APInt offset = APInt(pointerSize,0);
  Value* strip = val->stripAndAccumulateInBoundsConstantOffsets(wM->getDataLayout(),offset);
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
      CallSite call(strip);
      Function* calledFun = getStripCall(&call);
      if (calledFun && (calledFun->getName().equals("malloc") ||
			calledFun->getName().equals("MyMalloc"))) {
	if (escapeCheck(strip)) {
	  toReturn.insert(make_pair((Value*)NULL,list<int>(1,intoffset)));
	  //errs() << "Found escaped allocation: " << *inst << "\n";
	}
      }
      else {
	toReturn.insert(make_pair((Value*)NULL,list<int>(1,intoffset)));
	//errs() << "Found callsite: " << *inst << "\n";
      }
    }
  }
  if (auto glob = dyn_cast<GlobalVariable>(strip)) {
    //errs() << "Found global: " << *glob << "\n";
    toReturn.insert(make_pair(glob,list<int>(1,intoffset)));
  }
  if (auto arg = dyn_cast<Argument>(strip)) {
    //errs() << "Found argument: " << *arg << "\n";
    toReturn.insert(make_pair((Value*)NULL,list<int>(1,intoffset)));
  }

  //These are the recursive cases, they add pointers to nextPointers
  //and define how to merge offsets
  if (auto load = dyn_cast<LoadInst>(strip)) {
    nextPointers.insert(load->getPointerOperand());
  }
  if (auto dyngep = dyn_cast<GetElementPtrInst>(strip)) {
    nextPointers.insert(dyngep->getPointerOperand());
    appendOffset = false;
    if (AssumeDGEPAliasConstBase) {
      if (!handleDynamicGEP(&strip,offset)) {
	if (!AssumeDGEPNoAlias) {
	  intoffset = -1;
	} else
	  nextPointers.erase(dyngep->getPointerOperand());
      } else {
	intoffset = offset.getLimitedValue();
      }
    } else {
      if (!AssumeDGEPNoAlias) {
	intoffset = -1;
      } else
	nextPointers.erase(dyngep->getPointerOperand());
    }
  }
  if (auto phi = dyn_cast<PHINode>(strip)) {
    appendOffset = false;
    for (Use &use : cast<PHINode>(strip)->incoming_values())
      nextPointers.insert(use.get());
  }

#define UNIFY_OFFSETS(X,Y) ((X == -1 || Y == -1) ? -1 : X+Y)

  for (Value* nextPoint : nextPointers) {
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
  }
#undef UNIFY_OFFSETS
  return toReturn;
}

set<pair<Value*,list<int> > > findBottomLevelValues(Value *val) {
  visitedBottomLevelValues.clear();
  return findBottomLevelValues_(val);
}

map<pair<Value*,Value*>, bool> pointerAliasDynamic;

bool pointerAlias(Value *pt1, Value *pt2) {
  if (pointerAliasDynamic.count(make_pair(pt1,pt2)) != 0)
    return pointerAliasDynamic[make_pair(pt1,pt2)];

  set<pair<Value*,list<int> > > bottomUsesPt1 = findBottomLevelValues(pt1);
  set<pair<Value*,list<int> > > bottomUsesPt2 = findBottomLevelValues(pt2);

  bool toReturn = false;

  for (set<pair<Value*,list<int> > >::iterator pt1pair = bottomUsesPt1.begin(),
	 end_pt1pair = bottomUsesPt1.end();
       pt1pair != end_pt1pair && !toReturn; ++pt1pair) {
    for (set<pair<Value*,list<int> > >::iterator pt2pair = bottomUsesPt2.begin(),
	   end_pt2pair = bottomUsesPt2.end();
	 pt2pair != end_pt2pair && !toReturn; ++pt2pair) {
      if (!pt1pair->first || !pt2pair->first) {
	toReturn = false;
	continue;
      }
      if (pt1pair->first != pt2pair->first)
	continue;
      auto pt1b = pt1pair->second.rbegin();
      auto pt2b = pt2pair->second.rbegin();
      bool listChecksOut = true;
      while (pt1b != pt1pair->second.rend() &&
	     pt2b != pt2pair->second.rend()) {
	if (*pt1b != -1 && *pt2b != -1 && *pt1b != *pt2b) {
	  listChecksOut = false;
	  break;
	}
	pt1b++;
	pt2b++;
      }
      if (pt1b != pt1pair->second.rend() ||
	  pt2b != pt2pair->second.rend())
	continue;
      if (listChecksOut) {
	toReturn = true;
      }
    }
  }
  return pointerAliasDynamic[make_pair(pt1,pt2)]=toReturn;
}

SmallPtrSet<Value*,1024> visitedAliasValues;

//Pointer comparsion
//Checks wether the pointer arguments to two instructions
//do not alias
bool pointerConflict(Instruction *P1, Instruction *P2, Module *M) {
  wM = M;
  SmallPtrSet<Value*,4> P1Pargs;
  SmallPtrSet<Value*,4> P2Pargs;
  if (auto P1_load = dyn_cast<LoadInst>(P1))
    P1Pargs.insert(P1_load->getPointerOperand());
  if (auto P1_store = dyn_cast<StoreInst>(P1))
                P1Pargs.insert(P1_store->getPointerOperand());
  if (auto P1_call = CallSite(P1))
    for (Use &arg : P1_call.args())
      if (isa<PointerType>(arg.get()->getType()))
	P1Pargs.insert(arg.get());
  if (auto P2_load = dyn_cast<LoadInst>(P2))
    P2Pargs.insert(P2_load->getPointerOperand());
  if (auto P2_store = dyn_cast<StoreInst>(P2))
                P2Pargs.insert(P2_store->getPointerOperand());
  if (auto P2_call = CallSite(P2))
    for (Use &arg : P2_call.args())
      if (isa<PointerType>(arg.get()->getType()))
	P2Pargs.insert(arg.get());
  bool toReturn = false;
  for (Value *P1a : P1Pargs) {
    if (toReturn)
      break;
    if(isa<PointerType>(P1a->getType()))
      for (Value *P2a : P2Pargs) {
	if (toReturn)
	  break;
	if (isa<PointerType>(P2a->getType()))
	  if (pointerAlias(P1a,P2a)) {
	    toReturn = true;
	  }
      }
  }
  return toReturn;
}
