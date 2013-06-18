// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __BASE_RANGE_H__
#define __BASE_RANGE_H__
//////////////////////////////////////////////////////////////////////////////
/// \file BaseRange.h
/// Generic class for range (interval) analyses.
///
/// This file contains common methods and attributes for the derived
/// classes Range and WrappedRange.
/// 
/// LLVM IR does not tag variables with signedness information. It
/// makes use of the two's complement representation, having the
/// advantage that addition, substraction, and multiplication behave
/// identical regardless the sign. For other sensitive operations like
/// sign extension, right shift, division or comparison operators
/// specialized LLVM instructions are used. 
///
/// This generic class assumes that the flag isSigned must be set at
/// front.
///
/// This class has a special symbol for top that represents
/// [-oo,+oo]. The reason is that we want to distinghish from the
/// cases between [MININT,MAXINT] and [-oo,+oo]. With the former
/// overflow is still possible but not with the latter.
///
/// Bottom is represented with the range [0,-1]. 
///////////////////////////////////////////////////////////////////////////////

// #define DEBUG_TYPE "RangeAnalysis"

#include "AbstractValue.h"
#include "Support/Utils.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/APInt.h"

using namespace llvm;

namespace unimelb {

  class BaseRange: public AbstractValue {
    /// The range of a program variable is an interval that consists
    /// of the minimum and maximun value (LB and UB) that the variable
    /// can be bound during the program's execution.
  protected: 
    APInt LB, UB;      //!< LB,UB \in [MININT,MAXINT]    
    /// \todo No need of using the attribute width. It is better to
    /// use the method getBitWidth() from APInt rather than the
    /// attribute width to avoid inconsistencies.
    unsigned width;    //!< width: 1,8,16,32,64
    /// Since LLVM is sign-agnostic we must take decision at front of
    /// making all integer signed or unsigned if wrapped
    /// intervals are not used. 
    /// If isSigned then ranges go from MININT=-2^{width-1} to
    /// MAXINT=2^{width-1}-1. Otherwise, from MININT=0 to
    /// MAXINT=2^{width}-1.
    bool isSigned; 
    bool __isTop;    //!< Arithmetic operations cannot modified the interval if true.
    public:      
    // Constructor
    BaseRange(Value *V, bool IsSigned, bool isLattice):  
      AbstractValue(V,isLattice) ,__isTop(true)
    {     
      isSigned = IsSigned;  
      unsigned Width = 0;
      Type * t = NULL;
      bool IsTrackableType = Utilities::getTypeAndWidth(var, t, Width);
      assert(IsTrackableType && "This should not happen!");
      width=Width;
      if (isSigned){
	setLB(APInt::getSignedMinValue(width));
	setUB(APInt::getSignedMaxValue(width));	 
      }
      else{
	setLB(APInt::getMinValue(width));
	setUB(APInt::getMaxValue(width));	 
      }	
    }
      
    // Constructor for an integer constant
    BaseRange(const ConstantInt *C,unsigned Width, bool IsSigned, bool isLattice): 
    AbstractValue(isLattice), __isTop(false){
      isSigned = IsSigned; 
      width = Width;
      setLB(C->getValue());
      setUB(C->getValue());
    }

    // Constructor for an integer constant
    BaseRange(APInt c,unsigned Width, bool IsSigned, bool isLattice): 
    AbstractValue(isLattice),__isTop(false){
      isSigned = IsSigned; 
      width = Width;
      setLB(c);
      setUB(c);
    }

    // Constructor for APInt's (this is only for temporary results!)
    BaseRange(APInt lb, APInt ub, unsigned Width, bool IsSigned, bool isLattice): 
    AbstractValue(isLattice),__isTop(false){
      isSigned = IsSigned; 
      width = Width;
      setLB(lb);
      setUB(ub);
    }

    // Copy constructor
    BaseRange(const BaseRange& I ): 
    AbstractValue(I){
      width=I.width;
      isSigned=I.isSigned;
      setLB(I.LB);
      setUB(I.UB);
      __isTop = I.__isTop;
    }

    // Destructor
    virtual ~BaseRange(){}

    //Access methods
    inline APInt getUB()      { return UB;}
    inline APInt getLB()      { return LB;}
    inline APInt getUB() const{ return UB;}
    inline APInt getLB() const{ return LB;}

    inline unsigned getWidth(){ return width;}
    inline bool IsSigned() const { return isSigned;}

    inline bool IsConstantRange() const{
      if (isBot()) return false;
      if (IsTop()) return false;
      return (getLB() == getUB());
    }

    inline bool IsZeroRange() const{
      if (IsConstantRange()){
	return (getLB() == 0);
      }
      return false;
    }

    /////////////////////////////////////////////////////////////////////
    // Functions to call signed or unsigned version depending on the
    // sign of the BaseRange object or the instruction
    /////////////////////////////////////////////////////////////////////
    inline APInt getMaxValue(){
      if (isSigned)
    	return APInt::getSignedMaxValue(width);
      else
    	return APInt::getMaxValue(width);
    }
    inline APInt getMinValue(){
      if (isSigned)
    	return APInt::getSignedMinValue(width);
      else
    	return APInt::getMinValue(width);
    }
    static inline bool IsSignedCompInst(unsigned Opcode) {
      switch(Opcode){
      case ICmpInst::ICMP_SLE:
      case ICmpInst::ICMP_SLT:	
      case ICmpInst::ICMP_SGE:
      case ICmpInst::ICMP_SGT:	
    	return true;	
      default:	
	return false;
      }
    }
      
    inline APInt getMaxValue(unsigned Opcode){
      if (IsSignedCompInst(Opcode))
    	return APInt::getSignedMaxValue(width);	
      else
	return APInt::getMaxValue(width);
    }

    inline APInt getMinValue(unsigned Opcode){
      if (IsSignedCompInst(Opcode))
    	return APInt::getSignedMinValue(width);	
      else
	return APInt::getMinValue(width);
    }

    inline bool bridge_le(unsigned Opcode, APInt a, APInt b){
      if (IsSignedCompInst(Opcode))
	return a.sle(b);
      else
	return a.ule(b);
    }

    inline bool bridge_lt(unsigned Opcode, APInt a, APInt b){
      if (IsSignedCompInst(Opcode))
	return a.slt(b);
      else
	return a.ult(b);
    }

    inline bool bridge_ge(unsigned Opcode, APInt a, APInt b){
      if (IsSignedCompInst(Opcode))
	return a.sge(b);
      else
	return a.uge(b);
    }

    // Modifier methods    
    virtual inline void setLB(APInt lb)   { LB=lb; }
    virtual inline void setUB(APInt ub)   { UB=ub; }
    virtual inline void setLB(uint64_t lb){ LB=lb; }
    virtual inline void setUB(uint64_t ub){ UB=ub; }

    inline void setSign(bool IsSigned){
      isSigned = IsSigned;
    }

    inline void setWidth(unsigned Width)  { width=Width; }

    inline void RangeAssign(BaseRange * V) {
      setLB(V->getLB());
      setUB(V->getUB());
      __isTop = V->IsTop();
    }

    inline void resetTopFlag(){
      __isTop=false;
    }

    /// Return true is the element is top.
    virtual bool IsTop() const;
    /// Make top the element.
    virtual void makeTop();
    /// Print the abstract element.
    virtual void print(raw_ostream &) const;

    // Common operations in derived classes.

    /// Return true is this is syntactically identical to V.
    virtual bool isIdentical(AbstractValue *V);

    /// Print an interval.
    void printRange(raw_ostream &) const;
          
    /// Return true if the signed intervals [lb1,ub1]
    /// and [lb2,ub2] are disjoint.
    static bool signedIsDisjoint(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      // is_disjoint([a,b],[c,d]) if b < c or d < a
      return (ub1.slt(lb2) || ub2.slt(lb1));
    }   

    /// Return true if the unsigned intervals [lb1,ub1] and
    /// [lb2,ub2] are disjoint.
    static bool IsDisjoint(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      return (ub1.ult(lb2) || ub2.ult(lb1));
    }

    /// is_included([a,b],[c,d]) if a>=c && b <=d
    /// a,b,c,d are signed.
    static bool signedIsIncluded(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      return (lb1.sge(lb2) && ub1.sle(ub2));
    }

    /// is_included([a,b],[c,d]) if a>=c && b <=d
    /// a,b,c,d are unsigned.
    static bool IsIncluded(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      return (lb1.uge(lb2) && ub1.ule(ub2));
    }

    /// is_overlap_right([a,b],[c,d]) if c <= b && d > b
    /// a,b,c,d are signed.
    static bool signedIsOverlapRight(APInt lb1, APInt ub1, APInt lb2, APInt ub2){      
      return (lb2.sle(ub1) && ub2.sgt(ub1));
    }

    /// is_overlap_right([a,b],[c,d]) if c <= b && d > b
    /// a,b,c,d are unsigned.
    static bool IsOverlapRight(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      return (lb2.ule(ub1) && ub2.ugt(ub1));
    }

    /// is_overlap_left([a,b],[c,d]) if c < a && d >= a
    /// a,b,c,d are signed.
    static bool signedIsOverlapLeft(APInt lb1, APInt ub1, APInt lb2, APInt ub2){      
      return (lb2.slt(lb1) && ub2.sge(lb1));
    }

    /// is_overlap_left([a,b],[c,d]) if c < a && d >= a
    /// a,b,c,d are unsigned.
    static bool IsOverlapLeft(APInt lb1, APInt ub1, APInt lb2, APInt ub2){
      return (lb2.ult(lb1) && ub2.uge(lb1));
    }

    /// As IsOverlapLeft but taking the cases if signed or unsigned.
    static bool bridge_IsOverlapLeft(unsigned opCode,
				     APInt a, APInt b, APInt c, APInt d){
      if (opCode == ICmpInst::ICMP_ULT ||  
	  opCode == ICmpInst::ICMP_ULE || 
	  opCode == ICmpInst::ICMP_UGT || 
	  opCode == ICmpInst::ICMP_UGE){
	return IsOverlapLeft(a,b,c,d);
      }
      if (opCode == ICmpInst::ICMP_SLT ||  
	  opCode == ICmpInst::ICMP_SLE || 
	  opCode == ICmpInst::ICMP_SGT || 
	  opCode == ICmpInst::ICMP_SGE){
	return signedIsOverlapLeft(a,b,c,d);
      }  
      assert(false && "uncovered case in bridge_IsOverlapLeft");
    }

    /// As IsOverlapRight but taking the cases if signed or unsigned.
    static bool bridge_IsOverlapRight(unsigned opCode,
				      APInt a, APInt b, APInt c, APInt d){
      if (opCode == ICmpInst::ICMP_ULT ||  
	  opCode == ICmpInst::ICMP_ULE || 
	  opCode == ICmpInst::ICMP_UGT || 
	  opCode == ICmpInst::ICMP_UGE){
	return IsOverlapRight(a,b,c,d);
      }
      if (opCode == ICmpInst::ICMP_SLT ||  
	  opCode == ICmpInst::ICMP_SLE || 
	  opCode == ICmpInst::ICMP_SGT || 
	  opCode == ICmpInst::ICMP_SGE){
	return signedIsOverlapRight(a,b,c,d);
      }  
      assert(false && "uncovered case in bridge_IsOverlapRight");
    }

    // As IsIncluded but considering if signed or unsigned.
    static bool bridge_IsIncluded(unsigned opCode,
				  APInt a, APInt b, APInt c, APInt d){
      if (opCode == ICmpInst::ICMP_ULT ||  
	  opCode == ICmpInst::ICMP_ULE || 
	  opCode == ICmpInst::ICMP_UGT || 
	  opCode == ICmpInst::ICMP_UGE){
	return IsIncluded(a,b,c,d);
      }
      if (opCode == ICmpInst::ICMP_SLT ||  
	  opCode == ICmpInst::ICMP_SLE || 
	  opCode == ICmpInst::ICMP_SGT || 
	  opCode == ICmpInst::ICMP_SGE){
	return signedIsIncluded(a,b,c,d);
      }  
      assert(false && "uncovered case in bridge_IsIncluded");
    }

    /// Return false if some error condition with bitwise shift
    /// operations.
    bool checkOpWithShift(BaseRange *, BaseRange *);
    /// To check error conditions with casting operations.
    void checkCastingOp(const Type *,unsigned &,const Type *,unsigned &,
			const unsigned,unsigned);      

    // comparison operations 
    static APInt smin(APInt x, APInt y) { return x.slt(y) ? x : y;}
    static APInt smax(APInt x, APInt y) { return x.sgt(y) ? x : y;}
    static APInt umin(APInt x, APInt y) { return x.ult(y) ? x : y;}
    static APInt umax(APInt x, APInt y) { return x.ugt(y) ? x : y;}    

  };

  // bitwise operations 
  APInt minOr( APInt, APInt, APInt, APInt);
  APInt maxOr( APInt, APInt, APInt, APInt);
  APInt minAnd(APInt, APInt, APInt, APInt);
  APInt maxAnd(APInt, APInt, APInt, APInt);
  APInt minXor(APInt, APInt, APInt, APInt);
  APInt maxXor(APInt, APInt, APInt, APInt);

  void unsignedOr(BaseRange  *, BaseRange *,APInt &lb, APInt &ub); 
  void unsignedAnd(BaseRange *, BaseRange *,APInt &lb, APInt &ub); 
  void unsignedXor(BaseRange *, BaseRange *,APInt &lb, APInt &ub);
		      
} // End llvm namespace

#endif
