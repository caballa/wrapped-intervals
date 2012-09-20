// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __UTILITIES_H__
#define __UTILITIES_H__
///////////////////////////////////////////////////////////////////////////////
/// \file  Utils.h.
///        Some common utilities 
///////////////////////////////////////////////////////////////////////////////

#include "llvm/Value.h"
#include "llvm/Constants.h"
#include "llvm/Type.h"
#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace unimelb {

  class Utilities{
  public:
    /// If the type t is an integer then return its
    /// width (in Width) and return true. Otherwise, return false.
    static bool getIntegerWidth(const Type * t, unsigned &Width){      
      if (t->isIntegerTy(1))  Width=1;
      if (t->isIntegerTy(8))  Width=8;
      if (t->isIntegerTy(16)) Width=16;
      if (t->isIntegerTy(32)) Width=32;
      if (t->isIntegerTy(64)) Width=64;
      
      if ( (t->isIntegerTy(1))  || (t->isIntegerTy(8))  || 
	   (t->isIntegerTy(16)) || (t->isIntegerTy(32)) || (t->isIntegerTy(64)) ) 
	return true;
      else
	return false;      
    }
  
    /// If the value v is a pointer to an integer
    /// then return width of value (in Width) and return
    /// true. Otherwise, return false.
    static bool getPointerIntWidth(const Value *v, unsigned &Width){
      if (v->getType()->isPointerTy()){
	Type*  BasicT = v->getType()->getContainedType(0);
	return getIntegerWidth(BasicT,Width);
      }
      else
	return false;
    }
    
    /// Return true if the value v has a supported
    /// type. In that case, return also its type t and width.
    static bool getTypeAndWidth(Value *v, Type *&t, unsigned &Width){
      if (getIntegerWidth(v->getType(),Width)){
	t = v->getType();
	return true;
      }
      // Global variables are represented in LLVM IR as pointers
      if (GlobalVariable * gv = dyn_cast<GlobalVariable>(v)){
	if (getPointerIntWidth(gv,Width)){
	  t = gv->getType()->getContainedType(0);
	  return true;
	}
      }
      return false;
    }     


    /// Return true if the address of the value may be taken.
    /// Borrowed from SCCP.cpp.
    static bool AddressIsTaken(const GlobalValue *GV) {
      GV->removeDeadConstantUsers();
      
      for (Value::const_use_iterator UI = GV->use_begin(), E = GV->use_end();
	   UI != E; ++UI) {
	const User *U = *UI;
	if (const StoreInst *SI = dyn_cast<StoreInst>(U)) {
	  if (SI->getOperand(0) == GV || SI->isVolatile())
	    return true;  // Storing addr of GV.
	} else if (isa<InvokeInst>(U) || isa<CallInst>(U)) {
	  // Make sure we are calling the function, not passing the address.
	  ImmutableCallSite CS(cast<Instruction>(U));
	  if (!CS.isCallee(UI))
	    return true;
	} else if (const LoadInst *LI = dyn_cast<LoadInst>(U)) {
	  if (LI->isVolatile())
	    return true;
	} else if (isa<BlockAddress>(U)) {
	  // blockaddress doesn't take the address of the function, it takes addr
	  // of label.
	} else {
	  return true;
	}
      }
      return false;
    }

    /// Return true if the analysis will consider F.
    static bool IsTrackableFunction(const Function *F){  
      if (F == NULL)          return false;

      if (F->isDeclaration()) return false;

      if (F->hasFnAttr(Attribute::AlwaysInline)) return false;

      if (!F->mayBeOverridden()){
	if (AddressIsTaken(F)){
	  //DEBUG(dbgs() << "\t" << F->getName() << " is passed as a pointer.\n");
	  return false;
	}  
	else
	  return true;
      }
      else{
	//DEBUG(dbgs() << "\t" << F->getName() << " may be overriden.\n");
	return false;
      }
    }

  };
} // End namespace
#endif
