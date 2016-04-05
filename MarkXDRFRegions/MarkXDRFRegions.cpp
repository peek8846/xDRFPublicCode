//===-------------------- Marks nDRF and xDRF regions ---------------------===//
// Marks the source code with the beginning and end of nDRF and xDRF regions
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

#include "../XDRFExtension/XDRFExtension.cpp"

#define LIBRARYNAME "MarkXDRFRegions"

//Define moderately pretty printing functions
#define PRINTSTREAM errs()
#define PRINT PRINTSTREAM << "MarkXDRFRegions: "
#define PRINT_DEBUG PRINTSTREAM << "MarkXDRFRegions (debug): "

//Verbose prints things like progress
#define VERBOSE_PRINT(X) DEBUG_WITH_TYPE("verbose",PRINT << X)
//Light prints things like more detailed progress
#define LIGHT_PRINT(X) DEBUG_WITH_TYPE("light",PRINT << X)
//Debug should more accurately print exactly what is happening
#define DEBUG_PRINT(X) DEBUG_WITH_TYPE("debug",PRINT_DEBUG << X)

using namespace llvm;
using namespace std;

namespace {

    struct MarkXDRFRegions : public ModulePass {
        static char ID;
        MarkXDRFRegions() : ModulePass(ID) {
        }

    public:
        virtual void getAnalysisUsage(AnalysisUsage &AU) const{
            //AU.addRequired<AliasAnalysis>();
            AU.addRequired<XDRFExtension>();
            //Here we would "require" the previous AA pass
        }
      
        virtual bool runOnModule(Module &M) {
            XDRFExtension &xdrfextended  = getAnalysis<XDRFExtension>();

	    if (xdrfextended.nDRFRegions.size() == 0)
	      return false;

	    Function *beginNDRF = createDummyFunction("begin_NDRF",M);
	    Function *endNDRF = createDummyFunction("end_NDRF",M);
	    Function *beginXDRF = createDummyFunction("begin_XDRF",M);
	    Function *endXDRF = createDummyFunction("end_XDRF",M);

	    for (nDRFRegion * region : xdrfextended.nDRFRegions) {
	      for (Instruction * inst : region->beginsAt) {
		createDummyCall(beginNDRF,inst);
	      }
	      for (Instruction * inst : region->endsAt) {
		createDummyCall(endNDRF,inst,false);
	      }
	    }

            return true;
        }
    private:
      //Sets dummy to point to a function with name and a dummy implementation
      
      Function *createDummyFunction(string name, Module &M) {
	assert(!M.getFunction(name) && "Error creating dummy function, a function with that name already existed");
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
      
      void createDummyCall(Function* fun, Instruction* insertBef) {
	createDummyCall(fun,insertBef,true);
      }

      void createDummyCall(Function* fun, Instruction* insertBef, bool before) {
	vector<Value*> arglist;
	ArrayRef<Value*> args(arglist);
	CallInst* markCall = CallInst::Create(fun,args);
	if (before)
	  markCall->insertBefore(insertBef);
	else
	  markCall->insertAfter(insertBef);
      }
    };
}

char MarkXDRFRegions::ID = 0;
static RegisterPass<MarkXDRFRegions> Z("MarkXDRF",
				       "Marks nDRF and XDRF regions",
				       true,
				       true);

/* Local Variables: */
/* mode: c++ */
/* indent-tabs-mode: nil */
/* c-basic-offset: 4 */
/* End: */
