//===---- Defines Synchronization Points and Related Data Structures ------===//
// 
// 
//===----------------------------------------------------------------------===//
// Created at 1/2 -16
// Jonatan Waern
//===----------------------------------------------------------------------===//

#include <set>
#include <map>

#include "llvm/IR/Instruction.h"
#include "llvm/ADT/SmallPtrSet.h"

using namespace llvm;
using namespace std;

class SynchronizationPoint;

//A collection of synchronization points
class SynchronizationVariable {
public:
  SynchronizationVariable() {
    static int IDCount = 0;
    ID = IDCount++;
  }

  //Usefull for debugging
  int ID;

  //The constituent synchronization points
  SmallPtrSet<SynchronizationPoint*,8> synchronizationPoints;
  //The pairs of data conflicts (before, after) detected for this synchronization
  //variable
  set<pair<Instruction*,Instruction*> > conflicts;

  void merge(SynchronizationVariable *other);
};

//A point of synchronization in the program
class SynchronizationPoint {
public:
  SynchronizationPoint() {
    static int IDcount=0;
    ID = IDcount++;
  }

  //ID useful for debugging
  int ID;

  //The corresponding instruction
  Instruction *val;

  //What argument of the instruction is the memorylocation of synchronization
  int op=-1; //-1 Means that all arguments should be searched

  //The synchronization points that reach this without passing
  //over other synch points
  SmallPtrSet<SynchronizationPoint*,2> preceding;
  //For each preceding synchpoint, these are the instructions
  //that can be executed on the path leading here
  map<SynchronizationPoint*,SmallPtrSet<Instruction*,16> > precedingInsts;
  //The synchronization points reachable from this without
  //passing over other synch points
  SmallPtrSet<SynchronizationPoint*,2> following;
  //For each following synchpoint, these are the instructions
  //that can be executed on the path leading there
  map<SynchronizationPoint*,SmallPtrSet<Instruction*,16> > followingInsts;
  //The synchronization variable this is part of (if any)
  SynchronizationVariable *synchVar=NULL;

  //Returns a SmallPtrSet containing all points associated with this
  //point, including itself
  SmallPtrSet<SynchronizationPoint*,8> getAssociatedPoints() {
    if (synchVar)
      return synchVar->synchronizationPoints;
    else {
      SmallPtrSet<SynchronizationPoint*,8> toReturn;
      toReturn.insert(this);
      return toReturn;
    }
  }

  //Returns a SmallPtrSet containing all point associated with this
  //point, not including itself
  SmallPtrSet<SynchronizationPoint*,8> getOtherPoints() {
    SmallPtrSet<SynchronizationPoint*,8> toReturn;
    if (synchVar) {
      toReturn = synchVar->synchronizationPoints;
      toReturn.erase(this);
    }
    return toReturn;
  }
  //Sets the associated synchVar correctly
  void setSynchronizationVariable(SynchronizationVariable* other) {
    if (synchVar)
      synchVar->synchronizationPoints.erase(this);
    synchVar = other;
    synchVar->synchronizationPoints.insert(this);
  }
};

void SynchronizationVariable::merge(SynchronizationVariable *other) {
  for (SynchronizationPoint *synchPoint : other->synchronizationPoints) {
    synchPoint->setSynchronizationVariable(this);
  }
  conflicts.insert(other->conflicts.begin(),other->conflicts.end());
}
