// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __RANGE__H__
#define __RANGE__H__
//////////////////////////////////////////////////////////////////////////////
/// \file Range.h
///       Interval Abstract Domain.
///
/// This file contains the definition of the class Range,
/// which represents the classical interval abstract domain defined by
/// Cousot&Cousot'76 using fixed-width integers.
///
/// All operations here are sign-dependent. The choice of using
/// signed or unsigned semantics depends on the IsSigned() method in
/// BasicRange.
///
/// About top representation.
///
/// We distinguish between [MIN,MAX] and top. If an interval is top
/// any, e.g., arithmetic operation on it should return directly top
/// rather than doing weird things like performing the operation and
/// then producing overflow. If the interval is [MIN,MAX] still though
/// it has the same information we allow arithmetic operations operate
/// with it, producing possibly overflows.
///////////////////////////////////////////////////////////////////////////////

#include "AbstractValue.h"
#include "BaseRange.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/Attributes.h"
#include "llvm/Constants.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/Statistic.h"

// #define DEBUG_TYPE "RangeAnalysis"

namespace unimelb {

  /// Widening technique.
  typedef enum {NOWIDEN = 10, COUSOT76 = 11, JUMPSET = 12} WideningOpts;
  const WideningOpts  WideningMethod = JUMPSET; 

  class Range: public BaseRange {  
  public:          
    virtual BaseId getValueID() const { return RangeId; }

    /// Constructor of the class.
    Range(Value *V, bool IsSigned): BaseRange(V, IsSigned){}
    
    /// Constructor of the class.
    /// Creates a new object from an integer constant.
    Range(const ConstantInt *C, unsigned Width, bool IsSigned): 
    BaseRange(C,Width,IsSigned){ }

    /// Constructor of the class.
    /// Creates a new object from a TBool instance.
    Range(Value *V, TBool *B, bool IsSigned):
      BaseRange(V,IsSigned){
	if (B->isTrue()){
	  setLB(1); setUB(1);
	}
	else{
	  if (B->isFalse()){
	    setLB(0); setUB(0);
	  }
	  else{
	    // FIXME: we should say  [0,1]
	    makeTop();
	  }
	}
      }
    
    /// Copy constructor of the class.
    Range(const Range& I ): BaseRange(I){ }
    
    /// Clone method of the class.
    Range* clone(){
      return new Range(*this);
    }

    /// To support type inquiry through isa, cast, and dyn_cast.
    static inline bool classof(const Range *) { return true; }
    static inline bool classof(const BaseRange *V) {
      return (V->getValueID() == RangeId);
    }
    static inline bool classof(const AbstractValue *V) {
      return (V->getValueID() == RangeId);
    }

    /// Destructor of the class.
    ~Range(){}

    ///////////////////////////////////////////////////////////////////////
    /// Virtual methods defined in BaseRange.h
    ///////////////////////////////////////////////////////////////////////

    inline void setLB(APInt lb){ BaseRange::setLB(lb); }
    virtual inline void setUB(APInt ub){  BaseRange::setUB(ub); }
    virtual inline void setLB(uint64_t lb){  BaseRange::setLB(lb); }
    virtual inline void setUB(uint64_t ub){  BaseRange::setUB(ub); }

    /// Needed for presentation. Just to make sure that we have fair
    /// comparisons with other analyses.
    inline void normalize(){
      if (IsTop()) return;
      if (isBot()) return;
      if (isSigned){
    	if (getLB() == APInt::getSignedMinValue(width) &&
    	    getUB() == APInt::getSignedMaxValue(width)){
    	makeTop();
    	return;
    	}
      }
      else{
    	if (getLB() == APInt::getMinValue(width) &&
    	    getUB() == APInt::getMaxValue(width)){
    	  makeTop();
    	  return;
    	}
      }
    }


    // Abstract operations.
    virtual bool isBot() const;
    virtual bool IsTop() const;
    virtual void makeBot();
    virtual void makeTop();
    virtual bool lessOrEqual(AbstractValue * V);
    virtual void join(AbstractValue *V);
    virtual void meet(AbstractValue *V1,AbstractValue *V2);
    virtual bool isEqual(AbstractValue *V);
    virtual void widening(AbstractValue *, const SmallPtrSet<ConstantInt*, 16>); 
			  
    // Methods to evaluate a guard.
    virtual bool comparisonSle(AbstractValue *);
    virtual bool comparisonSlt(AbstractValue *);
    virtual bool comparisonUle(AbstractValue *);
    virtual bool comparisonUlt(AbstractValue *);

    virtual void filterSigma(unsigned, AbstractValue*,AbstractValue*);
    void filterSigma_TwoVars(unsigned, Range*,Range*);
    void filterSigma_VarAndConst(unsigned, Range*,Range*);

    // Abstract domain-dependent transfer functions 

    // addition, substraction, multiplication, signed/unsigned
    // division, signed/unsigned rem.
    virtual AbstractValue* visitArithBinaryOp(AbstractValue *, AbstractValue *,
					      unsigned, const char *);
    // and, or, xor, lsh, lshr, ashr
    virtual AbstractValue* visitBitwiseBinaryOp(AbstractValue *,AbstractValue *, 
						const Type *,const Type *,unsigned, const char *);
    // truncate and signed/unsigned extension
    virtual AbstractValue* visitCast(Instruction &, AbstractValue *, TBool*, bool);

    // virtual bool countForStats() const;
      
  };

} // End llvm namespace

#endif
