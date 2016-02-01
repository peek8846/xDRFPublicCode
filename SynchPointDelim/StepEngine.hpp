//===---- Utility class to enable instruction-level program-flow search ---===//
// Performs program-flow depth-first search of a function
// 
//===----------------------------------------------------------------------===//
// Created at 1/2 -16
// Jonatan Waern
//===----------------------------------------------------------------------===//

#include <deque>
#include "llvm/IR/Function.h"

class StepEngine {
  deque<Function*> stack;
}
