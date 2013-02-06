// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file RangeLattice.cpp
///       Interval Abstract Domain.
///
/// \todo There are many memory leaks: need to fix.
//////////////////////////////////////////////////////////////////////////////
#include "BaseRange.h"
#include "Range.h"

//#define DEBUG_TYPE "RangeAnalysis"

STATISTIC(NumOfOverflows     ,"Number of overflows");

using namespace llvm;
using namespace unimelb;

bool Range::isBot() const  { 
  return BaseRange::isBot();
}

bool Range::IsTop() const  { 
  return BaseRange::IsTop();
}

void Range::makeBot() { 
  BaseRange::makeBot();
}

void Range::makeTop() { 
  BaseRange::makeTop();
}

bool Range::lessOrEqual(AbstractValue * V){ 
  return BaseRange::lessOrEqual(V);
}

void Range::join(AbstractValue *V){
  BaseRange::join(V);
  // 09/10/12
  // normalize();
}

void Range::meet(AbstractValue *V1,AbstractValue *V2){
  assert(!isConstant() 
	 &&  "meet can be only called by a non-constant value");
  BaseRange::meet(V1,V2);
  // 09/10/12
  // normalize();

}

bool Range::isEqual(AbstractValue *V){
  return BaseRange::isEqual(V);
}

/// Compute the naive Cousot&Cousot'76 widening operation between two
/// ranges PreviousV and CurrentV and store the result in this.
/// widen([a,b],[c,d]) =  [l,h] where   
/// if b >= d then h=b else h=MAXINT
/// if a <= c then l=a else l=MININT
void wideningCousot77(Range *PreviousI, Range *CurrentI){

  assert(PreviousI->IsSigned() == CurrentI->IsSigned() 
	 && "Arguments must have same signedeness");

  if (PreviousI->IsSigned()){
    // signed case
    if (PreviousI->getUB().sge(CurrentI->getUB()))
      CurrentI->setUB(PreviousI->getUB());
    else{
      // (*) To push only the upper bound to MAXINT is not correct. We
      // need to cover also the case when the range may
      // wraparound. This is why we need to go to "top".
      // CurrentI->setUB(APInt::getSignedMaxValue(PreviousI->getWidth()));      
      CurrentI->makeTop();
    }    
    if (PreviousI->getLB().sle(CurrentI->getLB()))
      CurrentI->setLB(PreviousI->getLB());
    else{
      //  (*)
      // CurrentI->setLB(APInt::getSignedMinValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
  }
  else{
    // unsigned case
    if (PreviousI->getUB().uge(CurrentI->getUB()))
      CurrentI->setUB(PreviousI->getUB());
    else{
      // (*)
      // CurrentI->setUB(APInt::getMaxValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
    
    if (PreviousI->getLB().ule(CurrentI->getLB()))
      CurrentI->setLB(PreviousI->getLB());
    else{
      // (*)
      // CurrentI->setLB(APInt::getMinValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
  }      
}

/// Wrapper to call different widening methods.
void Range::widening(AbstractValue *PreviousV, 
			    const SmallPtrSet<ConstantInt*, 16> JumpSet){

  switch(WideningMethod){
  case NOWIDEN:
    return;
  case COUSOT76:
    assert(PreviousV != NULL);
    wideningCousot77(cast<Range>(PreviousV),this);
    DEBUG(dbgs() << "\tWIDENING (Cousot77) has been applied  " );
    DEBUG(print(dbgs()));
    DEBUG(dbgs() << "\n");    
    return;
  case JUMPSET:
    {
      APInt widenLB, widenUB;
      wideningJump(this, JumpSet, widenLB, widenUB);
      // Important step: to push only the upper (lower) bound to
      // MAXINT (MININT) is not correct.  If lb or ub is -oo or +oo,
      // we go to top.
      if (IsSigned() &&
	  (widenLB == APInt::getSignedMinValue(getWidth()) ||
	   widenUB == APInt::getSignedMaxValue(getWidth()))){
	makeTop();
	goto END;
      }      
      if ((!IsSigned()) && 
	  (widenLB == APInt::getMinValue(getWidth()) ||
	   widenUB == APInt::getMaxValue(getWidth()))){
	makeTop();  
	goto END;
      }      
      setLB(widenLB);
      setUB(widenUB);
    END:
      // 09/10/12
      // normalize();
      DEBUG(dbgs() << "\tWIDENING (based on jumps) has been applied  " );
      DEBUG(print(dbgs()));
      DEBUG(dbgs() << "\n");
    }
    return;
  default:
    assert(false && "ERROR: widening method not implemented\n");
  }
}
  
// These operations are used to determine if the evaluation of a guard
// is true or not. Note that these do not change the abstract value of
// the variable involved in the guard. This will be done by
// propagateSigmaVarConst and propagateSigmaTwoVars.

bool Range::comparisonSle(AbstractValue *V){
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  // [a,b] <= [c,d] if a <= d
  return I1->getLB().sle(I2->getUB());
}

bool Range::comparisonSlt(AbstractValue *V){				 
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  // [a,b] < [c,d]  if a < d 
  return I1->getLB().slt(I2->getUB());
}

bool Range::comparisonUle(AbstractValue *V){
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);

  APInt a = I1->getLB();
  APInt b = I1->getUB();
  APInt c = I2->getLB();
  APInt d = I2->getUB();

  // [a,b] <= [c,d] if a <= d
  if (IsSigned())
    return a.sle(d) || a.ule(d);
  else
    return a.ule(d);

}

bool Range::comparisonUlt(AbstractValue *V){				 
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  APInt a = I1->getLB();
  APInt b = I1->getUB();
  APInt c = I2->getLB();
  APInt d = I2->getUB();


  // [a,b] < [c,d]  if a < d 
  // Tricky cases: [-128,3] <_u [3,3] we should say yes!
  if (IsSigned())
    return a.slt(d);
  else
    return a.ult(d);
}

/// Refine the intervals of the variables V1 and V2 involved in a
/// guard once we know if the evaluation of the guard is true or
/// false.
void Range::filterSigma(unsigned Pred,  AbstractValue *V1, AbstractValue *V2){
  Range *Var1   = cast<Range>(V1);
  Range *Var2   = cast<Range>(V2);

  if (!Var1->isConstant() && Var2->isConstant()){
    assert(Var2->IsConstantRange() 
	   && "Some inconsistency found in filterSigma");
    filterSigma_VarAndConst(Pred, Var1, Var2);    			      
  } 
  else if (!Var1->isConstant() &&  !Var2->isConstant()){
      filterSigma_TwoVars(Pred, Var1, Var2);
  }
  else{
    assert(false && "Unexpected case in filterSigma");
  }
  // 09/10/12
  //normalize();
}

/// Case when one is variable and the other a constant in the branch
/// condition. V is the interval associated with the variable and N is
/// the interval associated with the constant.
void Range::filterSigma_VarAndConst(unsigned Pred, Range *V, Range *N){
  // Assumption: V is the range we would like to improve using     
  // information from Pred and N                                   
  Range *LHS = this;
  assert((!V->isConstant() && N->isConstant()) &&  (N->IsConstantRange()));

  switch (Pred){
  case ICmpInst::ICMP_EQ:
    { /* if v == n then [n,n] */       
      LHS->setLB(N->getLB());
      LHS->setUB(N->getUB());    
      return;
    }
  case ICmpInst::ICMP_NE:
    {
      // The only case to improve the range of V is in case N is
      // either the upper bound of V or its lower bound.  (Overflow is
      // not possible here. Assume overflow is possible, then the only
      // possibility of overflow would be if V=N=[MIN,MIN] and
      // V=N=[MAX,MAX]. But V cannot be equal to N)

      if (V->getLB() == N->getLB())
	LHS->setLB(V->getLB() + 1);      
      else
	LHS->setLB(V->getLB());

      if (V->getUB() == N->getUB())
	LHS->setUB(V->getUB() - 1);
      else
	LHS->setUB(V->getUB());          

      // tricky normalization step: if LHS is not improved and the
      // original value V was top then LHS must be kept as top.
      if (LHS->getLB() == V->getLB() && LHS->getUB() == V->getUB() && V->IsTop())
	LHS->makeTop();

      return;
    }
  case ICmpInst::ICMP_ULE:
  case ICmpInst::ICMP_SLE:
    { /* if v <= n then rng(v) /\ [-oo,n] */
      // prepare the range [-oo,n]
      Range *TmpRng = new Range(*N);
      TmpRng->setLB(getMinValue(Pred));
      LHS->meet(V,TmpRng);
      delete TmpRng;
      if (LHS->isBot()){
	// It's possible that V is less than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }
  case ICmpInst::ICMP_ULT:	  
  case ICmpInst::ICMP_SLT:	  
    { /* if v < n then rng(v) /\ [-oo,n-1] */
      // prepate the range [-oo,n-1]

      Range *TmpRng = new Range(*N);      
      TmpRng->setLB(getMinValue(Pred));
      // make sure we cannot have an overflow!
      if (N->getLB() == N->getMinValue()) // this method checks if it's signed or not
	TmpRng->setUB(N->getLB());   
      else
	TmpRng->setUB(N->getLB() - 1);         
      LHS->meet(V,TmpRng);
      delete TmpRng;
      if (LHS->isBot()){
	// It's possible that V is less than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }
  case ICmpInst::ICMP_UGT:
  case ICmpInst::ICMP_SGT:
    { /* if v > n then  rng(v) /\ [n+1,+oo] */ 
      // prepare range [n+1,+oo]
      Range *TmpRng = new Range(*N);
      TmpRng->setUB(getMaxValue(Pred));
      // make sure we cannot have an overflow!
      if (N->getUB() == N->getMaxValue()) // this method checks if it's signed or not
	TmpRng->setLB(N->getUB()); 
      else
	TmpRng->setLB(N->getUB() + 1);       
      LHS->meet(V,TmpRng);
      delete TmpRng;
      if (LHS->isBot()){
	// It's possible that V is greater than N, and V and N are
	// disjoint. In that case, we return the range of V
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }    
  case ICmpInst::ICMP_UGE:
  case ICmpInst::ICMP_SGE:
    { /* if v >= n then  rng(v) /\ [n,+oo] */ 
      // prepare the range [n,+oo]
      Range *TmpRng = new Range(*N);
      TmpRng->setUB(getMaxValue(Pred));
      TmpRng->setLB(N->getUB()); 		    		  
      LHS->meet(V,TmpRng);
      delete TmpRng;
      if (LHS->isBot()){
	// It's possible that V is greater than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }  
  default:
    assert(false && "unexpected error in filterSigma_VarAndConst");
  }
}

/// The condition of the branch involves two variables.
void Range::filterSigma_TwoVars(unsigned Pred, Range *I1, Range *I2){
  // Assumption: I1 is the range we would like to improve using
  // information from Pred and I2
  Range *LHS = this;
  assert(!I1->isConstant() &&  !I2->isConstant());
  assert((I1->IsSigned()   == I2->IsSigned()) &&
	 "Arguments must have same signedeness");

  // Special cases first
  if (I2->isBot()){ 
    // If I2 is bottom, we dont' have chance to improve I1
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  }
  if (I1->IsTop() && I2->IsTop()){
    LHS->makeTop();
    return;
  }

  LHS->meet(I1,I2);
  if (LHS->isBot()){
    // If I1 and I2 are disjoint we don't have chance to improve I1
    // E.g. [0,2] < [10,50]
    // The meet here is bottom so we cannot improve
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  }

  switch(Pred){
  case ICmpInst::ICMP_EQ: 
    // LHS is the meet between I1 and I2
    return;
  case ICmpInst::ICMP_NE:  
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());        
    // Minor improvement if I2 is a point
    if (I2->getLB() == I2->getUB()){ 
      if (I1->getLB() == I2->getLB())
	LHS->setLB(LHS->getLB()+1);
      if (I1->getUB() == I2->getUB())
	LHS->setUB(LHS->getUB()-1);
    }
    return;
  case ICmpInst::ICMP_ULT: // I1 <  I2
  case ICmpInst::ICMP_ULE: // I1 <= I2
  case ICmpInst::ICMP_SLT: // I1 <  I2
  case ICmpInst::ICMP_SLE: // I1 <= I2
    if (BaseRange::
	bridge_IsIncluded(Pred,I2->getLB(),I2->getUB(),I1->getLB(),I1->getUB())){
      // Case where we can improve further the meet: I2 is included in I1 
      // E.g., [-10,+oo] <= [-5,-2] --> [-10,-2]
      // E.g., [-10,+oo] <  [-5,-2] --> [-10,-3]
      LHS->setLB(I1->getLB());
      if (Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_ULT)
	LHS->setUB(I2->getUB() - 1);
      else
	LHS->setUB(I2->getUB());
      return;
    }
    if (BaseRange::
	bridge_IsOverlapLeft(Pred,I1->getLB(),I1->getUB(),I2->getLB(),I2->getUB())){
      // The result is the meet between I1 and I2
      return;
    }     
    // Otherwise, no improvement. That is, overlap-right or I1 included
    // in I2 cannot improve our knowledge about I1
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  case ICmpInst::ICMP_UGT: 
  case ICmpInst::ICMP_UGE: 
  case ICmpInst::ICMP_SGT: 
  case ICmpInst::ICMP_SGE: 
    if (BaseRange::
	bridge_IsIncluded(Pred,I2->getLB(),I2->getUB(),I1->getLB(),I1->getUB())){
      // Case where we can improve further the meet
      // E.g., [-10,+oo] >= [-5,-2] --> [-5,+oo]
      // E.g., [-10,+oo] >  [-5,-2] --> [-4,+oo]
      LHS->setUB(I1->getUB());
      if (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_UGE)
	LHS->setLB(I2->getLB());
      else
	LHS->setLB(I2->getLB()+1);	
      return;
    }
    if (BaseRange::
	bridge_IsOverlapRight(Pred,I1->getLB(),I1->getUB(),I2->getLB(),I2->getUB())){
      // The result is the meet between I1 and I2
      return;
    }
    // Otherwise, no improvement. That is, overlap-left or if I1 is
    // included in I2 do not provide new knowledge about I1
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  default: ;
  }
}

/// Compute the transfer function for arithmetic binary operators and
/// check for overflow. If overflow detected then top.
AbstractValue* Range::visitArithBinaryOp(AbstractValue* V1, AbstractValue* V2,
					 unsigned OpCode, const char * OpCodeName ){
			     
  Range *Op1 = cast<Range>(V1);
  Range *Op2 = cast<Range>(V2);
  Range *LHS = new Range(*this);

  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(Op1->printRange(dbgs()));
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs()));
  DEBUG(dbgs() << " = ");
  
  bool IsOverflow;
  BasicArithBinaryOp(LHS,Op1,Op2,OpCode,OpCodeName,IsOverflow);
  // Most arithmetic operations can raise overflow except unsigned
  // division and rem
  if (IsOverflow) {
    LHS->makeTop();
    NumOfOverflows++;
  }
  // 09/10/12
  // normalize();      
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");        
  
  return LHS;
}

/// Perform the transfer function for casting operations and check
/// overflow. If overflow detected then top.
AbstractValue * Range::visitCast(Instruction &I, AbstractValue * V, TBool * TB, bool IsSigned){

  Range *RHS = NULL;    
  if (!V){
    // Special case if the source is a Boolean Flag    
    assert(TB && "ERROR: visitCat assumes that TB != NULL");
    RHS = new Range(I.getOperand(0), TB, IsSigned); 
  }
  else{
    // Common case
    RHS = cast<Range>(V);    
    assert(!TB && "ERROR: some inconsistency found in visitCast");
  }

  Range *LHS = new Range(*this);
  bool IsOverflow;
  BasicCast(LHS, RHS, 
	    I.getOperand(0)->getType(), I.getType(), I.getOpcode(), 
	    IsOverflow);

  if (!V)
    delete RHS;

  // note that only Trunc (truncation) can raise overflow
  if (IsOverflow){
    LHS->makeTop(); 
    NumOfOverflows++;
  }
  // 09/10/12
  // normalize();    
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");      
  return LHS;

}

/// Perform the transfer function for bitwise operations and check
/// overflow. If overflow detected then top.
AbstractValue * Range:: visitBitwiseBinaryOp(AbstractValue * V1, AbstractValue * V2, 
					     const Type * Op1Ty, const Type * Op2Ty, 
					     unsigned OpCode,const char * OpCodeName){
  Range *Op1 = cast<Range>(V1);
  Range *Op2 = cast<Range>(V2);
  Range *LHS = new Range(*this);
  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(Op1->printRange(dbgs())); 
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs())); 
  DEBUG(dbgs() << " = ");
  
  bool IsOverflow;
  BasicBitwiseBinaryOp(LHS, Op1, Op2, Op1Ty, Op2Ty, OpCode, IsOverflow);
  // note that only Shl (left shift) can arise an overflow
  if (IsOverflow){  
    LHS->makeTop();
    NumOfOverflows++;
  }
  // 09/10/12
  // normalize();
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");        
  return LHS;  
}

    
