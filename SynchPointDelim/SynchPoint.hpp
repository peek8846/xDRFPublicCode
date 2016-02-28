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
class CriticalRegion;

//A collection of synchronization points
class SynchronizationVariable {
public:
  SynchronizationVariable() {
    static int IDCount = 0;
    ID = IDCount++;
  }

  //Usefull for debugging
  int ID;

  bool operator < (SynchronizationVariable other) const {
    return ID < other.ID;
  }

  //The constituent synchronization points
  SmallPtrSet<SynchronizationPoint*,8> synchronizationPoints;
  //The pairs of data conflicts (before, after) detected for this synchronization
  //variable
  //set<pair<Instruction*,Instruction*> > conflicts;

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

  bool operator < (SynchronizationPoint other) const {
    return ID < other.ID;
  }

  //The corresponding instruction
  Instruction *val;

  //Flags for checking specific attributes of synch points
  //The synch point begins an isolated region (e.g. an aquire of a lock)
  bool isCritBegin=false;
  bool isCritEnd=false;
  //The synch point is part of a one-way synchronization
  //(e.g. a signal would be FROM, a wait would be TO)
  bool isOnewayFrom=false;
  bool isOnewayTo=false;

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
  //The critical region this is part of (if any)
  CriticalRegion *critRegion=NULL;

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

  SmallPtrSet<Instruction*,128> getPrecedingInsts() {
    SmallPtrSet<Instruction*,128> toReturn;
    for (SynchronizationPoint* synchPoint : preceding)
      toReturn.insert(precedingInsts[synchPoint].begin(),
		      precedingInsts[synchPoint].end());
    return toReturn;
  }

  SmallPtrSet<Instruction*,128> getFollowingInsts() {
    SmallPtrSet<Instruction*,128> toReturn;
    for (SynchronizationPoint* synchPoint : following)
      toReturn.insert(followingInsts[synchPoint].begin(),
		      followingInsts[synchPoint].end());
    return toReturn;
  }


};

void SynchronizationVariable::merge(SynchronizationVariable *other) {
  for (SynchronizationPoint *synchPoint : other->synchronizationPoints) {
    synchPoint->setSynchronizationVariable(this);
  }
  //conflicts.insert(other->conflicts.begin(),other->conflicts.end());
}

//Describes a region of code which cannot be executed by more than 1 thread
//at a time. Basically a subset of the SynchronizationPoint graph
class CriticalRegion {
public:
  //The list of synch variables this Critical Region uses
  SmallPtrSet<SynchronizationVariable*,1> synchsOn;

  SmallPtrSet<SynchronizationPoint*,3> containedSynchPoints;
  SmallPtrSet<SynchronizationPoint*,1> entrySynchPoints;
  SmallPtrSet<SynchronizationPoint*,1> exitSynchPoints;

  void mergeWith(CriticalRegion* other) {
    other->containedSynchPoints.insert(containedSynchPoints.begin(),
				       containedSynchPoints.end());
    other->entrySynchPoints.insert(entrySynchPoints.begin(),
				   entrySynchPoints.end());
    other->exitSynchPoints.insert(exitSynchPoints.begin(),
				  exitSynchPoints.end());
    other->synchsOn.insert(synchsOn.begin(),
			   synchsOn.end());
    for (SynchronizationPoint* synchPoint : containedSynchPoints) {
      synchPoint->critRegion=other;
    }
  }
  
  SmallPtrSet<SynchronizationPoint*,2> getPrecedingRegions() {
    SmallPtrSet<SynchronizationPoint*,2> toReturn;
    for (SynchronizationPoint* synchPoint : entrySynchPoints) {
      toReturn.insert(synchPoint->preceding.begin(),
		      synchPoint->preceding.end());
    }
    return toReturn;
  }

  SmallPtrSet<SynchronizationPoint*,2> getFollowingRegions() {
    SmallPtrSet<SynchronizationPoint*,2> toReturn;
    for (SynchronizationPoint* synchPoint : exitSynchPoints) {
      toReturn.insert(synchPoint->following.begin(),
		      synchPoint->following.end());
    }
    return toReturn;
  }

  SmallPtrSet<Instruction*,128> getPrecedingInsts() {
    SmallPtrSet<Instruction*,128> toReturn;
    for (SynchronizationPoint* synchPoint : entrySynchPoints) {
      SmallPtrSet<Instruction*,128> preceding_ = synchPoint->getPrecedingInsts();
      toReturn.insert(preceding_.begin(),
		      preceding_.end());
    }
    return toReturn;
  }

  SmallPtrSet<Instruction*,128> getFollowingInsts() {
    SmallPtrSet<Instruction*,128> toReturn;
    for (SynchronizationPoint* synchPoint : exitSynchPoints) {
      SmallPtrSet<Instruction*,128> following_ = synchPoint->getFollowingInsts();
      toReturn.insert(following_.begin(),
		      following_.end());
    }
    return toReturn;
  }
};
