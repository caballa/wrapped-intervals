// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file BaseRange.cpp
///       Generic Range Variable Class
///
/// \todo There are many memory leaks: need to fix.
//////////////////////////////////////////////////////////////////////////////

#include "BaseRange.h"

using namespace llvm;
using namespace unimelb;

// Sanity check 
void CheckIntervalIsWellFormed(BaseRange *I){
  if (I->isBot() || I->IsTop()) return;

  if (I->IsSigned())
    assert(I->getLB().sle(I->getUB()));
  else
    assert(I->getLB().ule(I->getUB()));
}

/// Return true if the range is empty 
bool BaseRange::isBot() const{
  if (isConstant())  return false;      
  if (isSigned)
    return ((getLB() == APInt::getSignedMaxValue(width)) && 
	    (getUB() == APInt::getSignedMinValue(width)));
  else
    return ((getLB() == APInt::getMaxValue(width)) && 
	    (getUB() == APInt::getMinValue(width)));
}

/// Make an empty range.
void BaseRange::makeBot() {
  if (isSigned){
    setLB(APInt::getSignedMaxValue(width));
    setUB(APInt::getSignedMinValue(width));
  }
  else{
    setLB(APInt::getMaxValue(width));
    setUB(APInt::getMinValue(width));
  }
  __isTop=false;
}  

/// Return true is the range is top.
bool BaseRange::IsTop() const{  
  if (isConstant())  return false;
  return __isTop;

  // if (isSigned){
  //   return (getLB() == APInt::getSignedMinValue(width) &&
  // 	    getUB() == APInt::getSignedMaxValue(width));
  // }
  // else{
  //   return (getLB() == APInt::getMinValue(width) &&
  // 	    getUB() == APInt::getMaxValue(width)) ;
  // }
}


/// Make a range top.
void BaseRange::makeTop(){
  __isTop=true;

  // This is not actually needed but just in case ...
  if (isSigned){
    setLB(APInt::getSignedMinValue(width));
    setUB(APInt::getSignedMaxValue(width));
  }
  else{
    setLB(APInt::getMinValue(width)); 
    setUB(APInt::getMaxValue(width));
  }
}

/// Return true if the range of this is included in the the range of
/// V.
/// lessOrEqual([l1,u1],[l2,u2]) = true iff l2<=l1 and u1<=u2 
/// (i.e., [l1,u1] is included in [l2,u2])  
bool BaseRange::lessOrEqual(AbstractValue* V){
  // Simple cases first: bottom and top
  if (isBot())  return true;  
  BaseRange *I =  cast<BaseRange>(V);    
  if (IsTop() && I->IsTop()) 
    return true;
  else{
    if (IsTop())
      return false;
    else{
      if (I->IsTop()) 
	return true;
    }
  }
  // General case
  APInt l1 = getLB();
  APInt u1 = getUB();
  APInt l2 = I->getLB();
  APInt u2 = I->getUB();    
  assert(IsSigned() == I->IsSigned() 
	 && "Arguments must have same signedeness");
  if (I->IsSigned()) 
    return ( l2.sle(l1) &&  u1.sle(u2) );
  else 
    return ( l2.ule(l1) &&  u1.ule(u2) );
}

/// Return true if this and V have equal ranges.
bool BaseRange::isEqual(AbstractValue * V){
  BaseRange * B = cast<BaseRange>(V);
  return (__isTop == B->__isTop &&
	  getLB() == B->getLB() && getUB() == B->getUB());
}

/// Compute the join operation of two ranges and store the result in
/// this.  This operation is an overapproximation of the true union.
/// join([a,b],[c,d]) = [min(a,c),max(b,c)]
void BaseRange::join(AbstractValue * V){
  BaseRange *I2 = cast<BaseRange>(V);
  BaseRange *I1 = this;      
  // assert(I1->IsSigned() == I2->IsSigned() 
  //	 && "Arguments must have same signedeness");
  DEBUG(dbgs() << "\t");      
  DEBUG(I1->printRange(dbgs())); 
  DEBUG(dbgs() << " join " );
  DEBUG(I2->printRange(dbgs())); 
  DEBUG(dbgs() << " --> " );
  // Catch simple cases first (bottom, top)
  if (I1->isBot() && I2->isBot()){
    makeBot();
    goto END;
  }
  if (I1->IsTop() || I2->IsTop()){
    makeTop();
    goto END;
  }
  // General case:
  if (I1->isSigned){
    setLB(smin(I1->getLB(), I2->getLB()));
    setUB(smax(I1->getUB(), I2->getUB()));
    /////
    // This is needed to normalize "top"
    /////
    // 10/09/12
    // if ( (getLB() == APInt::getSignedMinValue(getLB().getBitWidth())) &&
    // 	 (getUB() == APInt::getSignedMaxValue(getLB().getBitWidth())))
    //   makeTop();
  }
  else{
    setLB(umin(I1->getLB(), I2->getLB()));
    setUB(umax(I1->getUB(), I2->getUB()));
    /////
    // This is needed to normalize "top"
    /////
    // 10/09/12
    // if ( (getLB() == APInt::getMinValue(getLB().getBitWidth())) &&
    // 	 (getUB() == APInt::getMaxValue(getLB().getBitWidth())))
    //   makeTop();
  }
    
 END:
  DEBUG(print(dbgs()));
  DEBUG(dbgs() << "\n");
}


/// Compute the meet operation of two ranges V1 and V2 This operation
/// is the exact intersection.
///
///                          if [a,b] or [c,d] is bot    then [l,h] = bot
/// meet([a,b],[c,d])=[l,h]  if is_disjoint([a,b],[c,d]) then [l,h] = bot
///                          else l = max(a,c) and h=min(b,d)
void BaseRange::meet(AbstractValue *V1, AbstractValue *V2){

  BaseRange *I1 = cast<BaseRange>(V1);
  BaseRange *I2 = cast<BaseRange>(V2);

  // Catch simple cases first 
  if (I1->isBot() || I2->isBot()){	
    makeBot();
    return;
  }

  if (I1->isSigned    && signedIsDisjoint(I1->getLB(),I1->getUB(),
					 I2->getLB(),I2->getUB())) {
    makeBot();
    return;
  }
  if ((!I1->isSigned) && IsDisjoint(I1->getLB(),I1->getUB(),
				    I2->getLB(),I2->getUB())) {
    makeBot();
    return;
  }  

  if (I1->isSigned){
    setLB(smax(I1->getLB(), I2->getLB()));    
    setUB(smin(I1->getUB(), I2->getUB()));
  }
  else{
    setLB(umax(I1->getLB(), I2->getLB()));
    setUB(umin(I1->getUB(), I2->getUB()));
  }
  
  return;
}

/// Display a range.
void BaseRange::printRange(raw_ostream &Out) const{
  if (isBot()){
    Out << "bottom" ; 
    return;
  } 
  if (IsTop()){
    Out << "[-oo,+oo]";
    return;
  }
  Out << "[" 
      << "u:" << LB.toString(10,false) <<"|"<< "s:" << LB.toString(10,true) << "," 
      << "u:" << UB.toString(10,false) <<"|"<< "s:" << UB.toString(10,true) << "]";
}

void BaseRange::print(raw_ostream &Out) const{  
  AbstractValue::print(Out);
  printRange(Out);
}

/// Compute the widening operation taking a "jump" making the interval
/// much wider. Compute a finite set of "jump points" J (e.g., the set
/// of all integer constants in the program augmented with MININT and
/// MAXINT). Then,
///  widen([l,u])=[max{x \in J | x <=l},min{x \in J,u <= x}]   
void BaseRange::wideningJump(BaseRange * Current, 
			     const SmallPtrSet<ConstantInt*, 16>  JumpSet,
			     APInt &lb, APInt &ub){
  assert(IsSigned() == Current->IsSigned() 
	 && "Arguments must have same signedeness");
  if (Current->IsSigned()){
    lb= APInt::getSignedMinValue(Current->getWidth());
    ub= APInt::getSignedMaxValue(Current->getWidth());
  }
  else{
    lb= APInt::getMinValue(Current->getWidth());
    ub= APInt::getMaxValue(Current->getWidth());
  }
  for (SmallPtrSet<ConstantInt*, 16>::iterator I=JumpSet.begin(), 
	 E=JumpSet.end(); I != E; ++I){    
    ConstantInt* C = *I;
    // We can have constants with different bit widths
    if (Current->getWidth() == C->getBitWidth()){
      APInt X = C->getValue();      
      if (Current->IsSigned()){
	if (Current->getLB().sge(X)) lb = BaseRange::smax(lb,X) ; 
	if (Current->getUB().sle(X)) ub = BaseRange::smin(ub,X) ;
      }
      else{
	if (Current->getLB().uge(X)) lb = BaseRange::umax(lb,X);
	if (Current->getUB().ule(X)) ub = BaseRange::umin(ub,X);
      }
    }
  }
}

/// Execute an arithmetic operation. Derived class will call this
/// method and do something else, in particular, how to deal with
/// overflow.
///
/// OVERFLOW NOTES: We detect arithmetic overflows in a post-morten
/// way. That is, we rely on the APInt class which perform the
/// arithmetic operations and then set up a flag to report if an
/// overflow occurred during the operations.
void BaseRange:: BasicArithBinaryOp(BaseRange *LHS,
				    BaseRange *Op1, BaseRange *Op2,
				    unsigned OpCode, const char *OpCodeName, 
				    bool &IsOverflow){
  IsOverflow = false;
  // First simple cases: bottom, top, etc.
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeBot();
    return;
  }
  if (Op1->IsTop() || Op2->IsTop()){
    LHS->makeTop();
    return;
  }
  assert(Op1->IsSigned() == Op2->IsSigned() &&
	 "Arguments must have same signedeness");

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  switch (OpCode){
  case Instruction::Add:
    {
      /// [a,b] + [c,d] = [a+c,b+d]
      bool OverflowLB,OverflowUB;
      if (Op1->IsSigned()){ 
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.sadd_ov(Op2->getLB(),OverflowLB));
	LHS->setUB(Op1->getUB());           
	LHS->setUB(LHS->UB.sadd_ov(Op2->getUB(),OverflowUB));
      }
      else{
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.uadd_ov(Op2->getLB(),OverflowLB));
	LHS->setUB(Op1->getUB());           
	LHS->setUB(LHS->UB.uadd_ov(Op2->getUB(),OverflowUB));
      }
      IsOverflow = (OverflowLB || OverflowUB);
      /* debugging info */
      if (IsOverflow){
	if (Op1->IsSigned()) DEBUG(dbgs() << " (signed overflow)");
	else                 DEBUG(dbgs() << " (unsigned overflow)");
      }

    }
    break;
  case Instruction::Sub:
    {
      // [a,b] - [c,d] = [a-d, b-c]
      bool OverflowLB,OverflowUB;
      if (Op1->IsSigned()){
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.ssub_ov(Op2->getUB(),OverflowLB));
	LHS->setUB(Op1->getUB());
	LHS->setUB(LHS->UB.ssub_ov(Op2->getLB(),OverflowUB));
      }
      else{
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.usub_ov(Op2->getUB(),OverflowLB));
	LHS->setUB(Op1->getUB());
	LHS->setUB(LHS->UB.usub_ov(Op2->getLB(),OverflowUB));
      }
      IsOverflow = (OverflowLB || OverflowUB);
      /* debugging info */      
      if (IsOverflow){
	if (Op1->IsSigned()) DEBUG(dbgs() << "(signed overflow) ");
	else                 DEBUG(dbgs() << "(unsigned overflow) ");
      }
    }
    break;
  case Instruction::Mul:
    {      
      if (Op1->IsZeroRange()){
	LHS->RangeAssign(Op1);
	break;
      }
      if (Op2->IsZeroRange()){
	LHS->RangeAssign(Op2);
	break;
      }      
      if (Op1->IsSigned())
	Mult_GeneralCase(true ,LHS, Op1, Op2, IsOverflow);
      else
	Mult_GeneralCase(false,LHS, Op1, Op2, IsOverflow);
    }
    break;
  case Instruction::UDiv:
  case Instruction::URem:
    {
      assert(!Op2->IsZeroRange() && "Unsigned division by zero!");
      if (Op1->IsZeroRange()){
	LHS->RangeAssign(Op1);
	break;
      }      
      UDivRem_GeneralCase(OpCode,LHS,Op1,Op2);
      // unsigned division/rem cannot raise overflow!
      IsOverflow=false;
    }
    break;      
  case Instruction::SDiv:
  case Instruction::SRem:
    {
      assert(!Op2->IsZeroRange() && "Signed division by zero!");
      if (Op1->IsZeroRange()){
	LHS->RangeAssign(Op1);
	break;
      }      
      DivRem_GeneralCase(OpCode,LHS,Op1,Op2,IsOverflow);
    }
    break;
  default:
    dbgs() << OpCodeName << "\n";
    assert(false && "Arithmetic operation not implemented");
  } // end switch

  // if (!IsOverflow){
  //   Op1->printRange(dbgs()); dbgs() << " <op> ";
  //   Op2->printRange(dbgs()); dbgs() << " =";
  //   LHS->printRange(dbgs()); dbgs() << "\n";
  //   CheckIntervalIsWellFormed(LHS);
  // }
}

/// [a,b] * [c,d] = [min(a*c,a*d,b*c,b*d),max(a*c,a*d,b*c,b*d)].
void BaseRange:: Mult_GeneralCase(bool IsSigned,
				  BaseRange *LHS, 
				  BaseRange *Op1, BaseRange *Op2,
				  bool &IsOverflow){
  APInt a,b,c,d;
  bool Overflow1,Overflow2,Overflow3,Overflow4;
  // FIXME: Do multiplications and overflow checks lazily
  if (IsSigned){
    a = Op1->getLB().smul_ov(Op2->getLB(),Overflow1);
    b = Op1->getLB().smul_ov(Op2->getUB(),Overflow2);
    c = Op1->getUB().smul_ov(Op2->getLB(),Overflow3);
    d = Op1->getUB().smul_ov(Op2->getUB(),Overflow4);
  }
  else{
    a = Op1->getLB().umul_ov(Op2->getLB(),Overflow1);
    b = Op1->getLB().umul_ov(Op2->getUB(),Overflow2);
    c = Op1->getUB().umul_ov(Op2->getLB(),Overflow3);
    d = Op1->getUB().umul_ov(Op2->getUB(),Overflow4);    
  }
  // FIXME: for simplicity if one of the above multiplications arises
  // overflow, we return overflow:
  IsOverflow = (Overflow1 || Overflow2 || Overflow3 || Overflow4);	
  // FIXME: if overflow arises then the below code may be useless
  // (e.g., for RangeLattice instances)
  if (IsSigned){
    LHS->setLB(smin(smin(smin(a,b),c),d));
    LHS->setUB(smax(smax(smax(a,b),c),d));
  }
  else{
    LHS->setLB(umin(umin(umin(a,b),c),d));
    LHS->setUB(umax(umax(umax(a,b),c),d));    
  }
  /* debugging info */      
  if (IsOverflow){
    if (IsSigned)
      DEBUG(dbgs() << "(signed overflow) ");  
    else
      DEBUG(dbgs() << "(unsigned overflow) ");	  
  }
}

// If v is 0 then it is replaced with 1. Otherwise, we just return the
// same APInt.  This is used to avoid too many false alarms but we
// could lose a real error .
inline APInt ReplaceZeroWithOne(APInt v){
  if (v == 0){
    return  APInt(v.getBitWidth(),1,false);
    //                               ^^^^^ unsigned
  }
  else
  return v;
}

/// [a,b] / [c,d] = [min(a/c,a/d,b/c,b/d),max(a/c,a/d,b/c,b/d)].
void BaseRange::DivRem_GeneralCase(unsigned OpCode,
		   BaseRange *LHS, 
		   BaseRange *Op1, BaseRange *Op2,
		   bool &IsOverflow){
  bool Overflow1,Overflow2,Overflow3,Overflow4;
  if (OpCode == Instruction::SDiv){
    // FIXME: not sure if the of ReplaceZeroWithOne is sound
    APInt a = Op1->getLB().sdiv_ov(ReplaceZeroWithOne(Op2->getLB()),Overflow1);
    APInt b = Op1->getLB().sdiv_ov(ReplaceZeroWithOne(Op2->getUB()),Overflow2);
    APInt c = Op1->getUB().sdiv_ov(ReplaceZeroWithOne(Op2->getLB()),Overflow3);
    APInt d = Op1->getUB().sdiv_ov(ReplaceZeroWithOne(Op2->getUB()),Overflow4);
    // FIXME: for simplicity if one of the above multiplications
    // arises overflow, we return overflow:      
    IsOverflow = (Overflow1 || Overflow2 || Overflow3 || Overflow4);	
    if (IsOverflow){
      DEBUG(dbgs() << "(signed overflow) ");
    }
    // FIXME: if overflow arises then the below code may be useless
    // (e.g., for RangeLattice instances)
    LHS->setLB(smin(smin(smin(a,b),c),d));
    LHS->setUB(smax(smax(smax(a,b),c),d));
    return;
  }

  if (OpCode == Instruction::SRem){
    // FIXME: not sure if the use of ReplaceZeroWithOne is sound.
    // Similar doubt than in  URem.

    APInt a = Op1->getLB().srem(ReplaceZeroWithOne(Op2->getLB()));
    APInt b = Op1->getLB().srem(ReplaceZeroWithOne(Op2->getUB()));
    APInt c = Op1->getUB().srem(ReplaceZeroWithOne(Op2->getLB()));
    APInt d = Op1->getUB().srem(ReplaceZeroWithOne(Op2->getUB()));
    LHS->setLB(smin(smin(smin(a,b),c),d));
    LHS->setUB(smax(smax(smax(a,b),c),d));

    IsOverflow=false;
    return;
  }
  assert(false && "Only for SDiv and SRem");
}

/// [a,b] / [c,d] = [min(a/c,a/d,b/c,b/d),max(a/c,a/d,b/c,b/d)].
void BaseRange::UDivRem_GeneralCase(unsigned OpCode,
		    BaseRange *LHS, 
		    BaseRange *Op1, BaseRange *Op2){
  if (OpCode == Instruction::UDiv){
    // FIXME: not sure if the of ReplaceZeroWithOne is sound
    APInt a = Op1->getLB().udiv(ReplaceZeroWithOne(Op2->getLB()));
    APInt b = Op1->getLB().udiv(ReplaceZeroWithOne(Op2->getUB()));
    APInt c = Op1->getUB().udiv(ReplaceZeroWithOne(Op2->getLB()));
    APInt d = Op1->getUB().udiv(ReplaceZeroWithOne(Op2->getUB()));
    LHS->setLB(umin(umin(umin(a,b),c),d));
    LHS->setUB(umax(umax(umax(a,b),c),d));  
    return;
  }
  if (OpCode == Instruction::URem){
    // FIXME: not sure if the of ReplaceZeroWithOne is sound

    // FIXME Ummm not sure this operation is correct. URem seems to be
    // like bitwise And, Or, and Xor where it is not enough to look at
    // the bounds to get a correct answer. 
    APInt a = Op1->getLB().urem(ReplaceZeroWithOne(Op2->getLB()));
    APInt b = Op1->getLB().urem(ReplaceZeroWithOne(Op2->getUB()));
    APInt c = Op1->getUB().urem(ReplaceZeroWithOne(Op2->getLB()));
    APInt d = Op1->getUB().urem(ReplaceZeroWithOne(Op2->getUB()));
    LHS->setLB(umin(umin(umin(a,b),c),d));
    LHS->setUB(umax(umax(umax(a,b),c),d));

    return;
  }
  assert(false && "ERROR: it covers only UDiv and URem instructions");
}

// Casting operations

/// Return true iff overflow during the truncate
/// operations. Overflow can happen if the interval does not fit into an
/// integer of destWidth bits.
bool BaseRange::IsTruncateOverflow(BaseRange * RHS, unsigned destWidth){
  // Note: overflow can happen both if the integer is signed or
  // unsigned. E.g. if the unsigned interval [000111,011011] is
  // truncated to 3 bits we would get [111,011] which is
  // wrapped. Therefore, we should return overflow since 0111011 does
  // not fit into 3 bits. (remember BaseRange assumes that
  // intervals cannot wraparound)

  // If LB is -oo or UB +oo then there is no overflow
  if (RHS->IsSigned()){
    return (((RHS->getUB().sgt(APInt::getSignedMaxValue(destWidth).getSExtValue()))) ||
	    ((RHS->getLB().slt(APInt::getSignedMinValue(destWidth).getSExtValue()))));
  }
  else{
    return (((RHS->getUB().ugt(APInt::getMaxValue(destWidth).getZExtValue()))) ||
	    ((RHS->getLB().ult(APInt::getMinValue(destWidth).getZExtValue()))));
  }  
}

/// Check error conditions during casting operations.
void BaseRange::
checkCastingOp(const Type *srcTy, unsigned &srcWidth, const Type *destTy, unsigned &destWidth,
		    const unsigned OpCode, unsigned ToBeCastWidth){

  assert((Utilities::getIntegerWidth(srcTy ,srcWidth) &&
	  Utilities::getIntegerWidth(destTy,destWidth)) &&
	 "ERROR: allow casting only of integers");  	  
  assert(ToBeCastWidth == srcWidth && "ERROR: violation of some cast precondition");	 
  if (OpCode == Instruction::Trunc)
    assert(srcWidth >= destWidth && "ERROR: violation of Trunc precondition");
  if ((OpCode == Instruction::SExt) || (OpCode == Instruction::ZExt))
    assert(srcWidth <= destWidth && "ERROR: violation of SExt/ZExt precondition");
}

/// Perform casting operations. Derived classes will do something
/// else, in particular, in case of overflow.
void BaseRange::BasicCast(BaseRange *LHS, BaseRange *RHS, 
			  const Type *srcTy, const Type *destTy, 
			  const unsigned OpCode,bool &IsOverflow){
  IsOverflow=false;

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  unsigned srcWidth,destWidth;  
  assert(LHS->IsSigned() == RHS->IsSigned() &&
	 "Arguments must have same signedeness");
  checkCastingOp(srcTy, srcWidth, destTy, destWidth, OpCode, RHS->getWidth());
  //  Perform casting                             
  LHS->setWidth(destWidth);        
  // Simple cases first: bottom and top
  if (RHS->isBot()){
    LHS->makeTop(); // be conservative
    return;
    }    
  if (RHS->IsTop()){
    LHS->makeTop();
    IsOverflow=false;
    return;
  }
  switch(OpCode) {
  case Instruction::Trunc:
    
    if (IsTruncateOverflow(RHS,destWidth)){
      DEBUG(dbgs() << "\tCast: truncating an integer that does not fit in the destination " 
	    << destWidth << " bits.\n");	
      IsOverflow=true;
    }
    // Even if overflow we perform trunc operation from APInt The
    // caller is in charge to decide what to do.  E.g., Range will
    // make it to top but WrappedRange will leave it.
    LHS->setUB(RHS->getUB().trunc(destWidth)); 
    LHS->setLB(RHS->getLB().trunc(destWidth)); 	  
    break;
  case Instruction::SExt:
    // apply sext from APInt
    LHS->setLB(RHS->getLB().sext(destWidth));
    LHS->setUB(RHS->getUB().sext(destWidth));    
    break;
  case Instruction::ZExt:
    // apply sext from APInt
    LHS->setLB(RHS->getLB().sext(destWidth));
    LHS->setUB(RHS->getUB().sext(destWidth));    
    break;
  case Instruction::BitCast:
    assert(srcWidth == destWidth && "ERROR: violation of BitCast precondition");
    // simply assign rhs to lhs
    LHS->setLB(RHS->getLB());
    LHS->setUB(RHS->getUB());    
    break;
  default:
    assert(false && "ERROR: unknown instruction in BasicCast");
  }  

  // CheckIntervalIsWellFormed(LHS);
}

/// Bitwise operations 


// Return true if all conditions about Shift holds.
bool BaseRange::
checkOpWithShift(BaseRange * Op, BaseRange * Shift){  
  // Here just sanity checks
  assert( (Op->getWidth() == Shift->getWidth()) && 
	  "Bitwise operands must have same width");
            // "LB Shift cannot be negative!"
  return (  (!Shift->getLB().isNegative()) &&
	    // "UB Shift cannot be negative!"
	    (!Shift->getUB().isNegative()) &&
	    // "UB Shift cannot be bigger than width!"
	    (Shift->getUB().slt(Op->getWidth())) &&
	    // "Shift does not fit into a uint64_t"
	    (Shift->getWidth() <= 64)  );

} 

void BaseRange:: BasicBitwiseShifts(BaseRange *LHS, 
				    BaseRange *Operand, BaseRange * Shift,
				    unsigned OpCode, bool &IsOverflow){
  if (Operand->isBot() || Shift->isBot()){
    LHS->makeTop(); // be conservative here
    return;
  }
  if (Operand->IsTop()){
    LHS->makeTop(); // FIXME: this case can be improved
    return;
  }
  if (!checkOpWithShift(Operand, Shift)){
    LHS->makeTop();
    return;
  }

  // At this point Shift is to be known as an interval between 0 and
  // 64.
  IsOverflow =false;
  switch(OpCode){
    // We compute Shl, LShr, and AShr as follows
    // [a,b] Op [c,d] =  [min({a Op c, a Op d, b Op c, b Op d}, 
    //                    max({a Op c, a Op d, b Op c, b Op d}) ]
  case Instruction::Shl:
    {
      // Shl can raise overflow

      ///
      // IMPORTANT: this implementation works also if the shift is not a
      // constant. However, we return top if the shift is not constant
      // in order to have a fair comparison with WrappedRange which does
      // not implementt that case.
      ///
      if (Shift->IsConstantRange()){
	if (Operand->IsSigned()){
	  bool Overflow1;
	  bool Overflow2;
	  bool Overflow3;
	  bool Overflow4;
	  APInt a    = Operand->getLB();
	  APInt b    = Operand->getUB();
	  // At this point we know the shift is positive so we can use
	  // unsigned extension
	  uint64_t c = (unsigned) Shift->getLB().getZExtValue();
	  uint64_t d = (unsigned) Shift->getUB().getZExtValue();	
	  APInt tmp1 = a.sshl_ov(c,Overflow1);
	  APInt tmp2 = a.sshl_ov(d,Overflow2);
	  APInt tmp3 = b.sshl_ov(c,Overflow3);
	  APInt tmp4 = b.sshl_ov(d,Overflow4);
	  LHS->setLB(smin(tmp1,smin(tmp2,smin(tmp3,tmp4))));
	  LHS->setUB(smax(tmp1,smax(tmp2,smax(tmp3,tmp4))));
	  IsOverflow = (Overflow1 || Overflow2 || Overflow3 || Overflow4);	            	
	}
	else{
	  // Overflow is not possible if unsigned.
	  LHS->setLB(Operand->getLB() << Shift->getLB());
	  LHS->setUB(Operand->getUB() << Shift->getUB());
	}
      }
      else
	LHS->makeTop();
    }
    break;
    // No overflow operations
  case Instruction::LShr:
    ///
    // IMPORTANT: this implementation works also if the shift is not a
    // constant. However, we return top if the shift is not constant
    // in order to have a fair comparison with WrappedRange which does
    // not implementt that case.
    ///
    if (Shift->IsConstantRange()){
      if (Operand->IsSigned()){
	APInt a = Operand->getLB();
	APInt b = Operand->getUB();
	APInt c = Shift->getLB();
	APInt d = Shift->getUB();	
	APInt tmp1 = a.lshr(c);
	APInt tmp2 = a.lshr(d);
	APInt tmp3 = b.lshr(c);
	APInt tmp4 = b.lshr(d);
	LHS->setLB(smin(tmp1,smin(tmp2,smin(tmp3,tmp4))));
	LHS->setUB(smax(tmp1,smax(tmp2,smax(tmp3,tmp4))));
      }
      else{
	LHS->setLB(Operand->getLB().lshr(Shift->getUB()));
	LHS->setUB(Operand->getUB().lshr(Shift->getLB()));	      
      }
    }
    else
      LHS->makeTop();

    break;
  case Instruction::AShr:
    ///
    // IMPORTANT: this implementation works also if the shift is not a
    // constant. However, we return top if the shift is not constant
    // in order to have a fair comparison with WrappedRange which does
    // not implement that case.
    ///
    if (Shift->IsConstantRange()){
      if (Operand->IsSigned()){
	APInt a = Operand->getLB();
	APInt b = Operand->getUB();
	APInt c = Shift->getLB();
	APInt d = Shift->getUB();	
	APInt tmp1 = a.ashr(c);
	APInt tmp2 = a.ashr(d);
	APInt tmp3 = b.ashr(c);
	APInt tmp4 = b.ashr(d);
	LHS->setLB(smin(tmp1,smin(tmp2,smin(tmp3,tmp4))));
	LHS->setUB(smax(tmp1,smax(tmp2,smax(tmp3,tmp4))));
      }
      else{
	LHS->setLB(Operand->getLB().ashr(Shift->getUB()));
	LHS->setUB(Operand->getUB().ashr(Shift->getLB()));	      
      }
    }
    else
      LHS->makeTop();
    break;
  default:
    assert(false && "bitwise shift operation not implemented");
  } // end switch;      
}


void BaseRange::BasicLogicalBitwise(BaseRange *LHS, 
				    BaseRange *Op1, BaseRange *Op2,
				    unsigned Opcode){
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeTop(); // be conservative here
    return;
  }
  // FIXME: this case can be improved!
  if (Op1->IsTop() || Op2->IsTop()){
    LHS->makeTop();
    return;
  }
  switch (Opcode){
  case Instruction::Or:    
    if (Op1->IsZeroRange())
      LHS->RangeAssign(Op2);
    else if (Op2->IsZeroRange())
      LHS->RangeAssign(Op1);
    else{
      // TODO: more base cases
      if (isSigned) LHS->signedOr(Op1,Op2);
      else          LHS->unsignedOr(Op1,Op2);
    }
    break;
  case Instruction::And:
    if (Op1->IsZeroRange())
      LHS->RangeAssign(Op1);
    else if (Op2->IsZeroRange())
      LHS->RangeAssign(Op2);
    else{
      // TODO: more base cases
      if (isSigned) LHS->signedAnd(Op1,Op2);
      else          LHS->unsignedAnd(Op1,Op2);
    }
    break;
  case Instruction::Xor:
    // TODO: more base cases
    if (isSigned) LHS->signedXor(Op1,Op2);
    else          LHS->unsignedXor(Op1,Op2);
    break;
  default:     
    assert(false && "This should not happen");
  } // end switch  
}

/// Perform bitwise operations.  
void BaseRange:: BasicBitwiseBinaryOp(BaseRange * LHS, 
				      BaseRange * Op1, BaseRange * Op2, 
				      const Type * Op1Ty, const Type * Op2Ty, 
				      unsigned OpCode, bool &IsOverflow){	 
  assert(OpCode == Instruction::And  || OpCode == Instruction::Or || 
	 OpCode == Instruction::Xor  || OpCode == Instruction::Shl ||
	 OpCode == Instruction::LShr || OpCode == Instruction::AShr );
  assert(Op1->IsSigned() == Op2->IsSigned() &&
	 "Arguments must have same signedeness");
  IsOverflow=false;
  // bottom and top are treated by callee methods

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  switch(OpCode){
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
    BasicBitwiseShifts(LHS,Op1,Op2,OpCode,IsOverflow);
    break;
  case Instruction::Or:
  case Instruction::And:
  case Instruction::Xor:
    BasicLogicalBitwise(LHS, Op1, Op2, OpCode);
    break;
  default: ;
  } // end switch  
  //CheckIntervalIsWellFormed(LHS);
}

/// x=[a,b] and y=[c,d] Reduce the value of x | y by increasing the
/// value of a or c.  We scan a and c from left to right. If both are
/// 1's or 0's then we continue with the scan of the next bit. If one
/// is 1 and the other is 0 then we change the 0 to 1 and set all the
/// following bits to 0's. If that value is less or equal than the
/// corresponding upper bound (if we change a then we compare with c,
/// otherwise we compare with d) we are done. Otherwise, we continue.
APInt minOr(APInt a, APInt b, APInt c, APInt d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((~a & c & m).getBoolValue()){
      APInt temp = (a | m) & ~m;
      if (temp.ule(b)){
	a = temp;
	break;
      }
    }
    else{
      if ((a & ~c & m).getBoolValue()){
	APInt temp = (c | m) & ~m;
	if (temp.ule(d)){
	  c =temp;
	  break;
	}
      }
    }
    m = m.lshr(1);
  }
  return a | c;
}

/// x=[a,b] and y=[c,d] Increase the value of x | y by decreasing the
/// value of b or d We scan b and d from left to right. If both are
/// 1's then change one to 0 and replace the subsequent bits to
/// 1's. If this value is greater or equal than the corresponding
/// lower bound we are done and the result is b | d. If the change
/// cannot be done we try with the other. If not yet, we continue with
/// the scan.
APInt maxOr(APInt a, APInt b, APInt c, APInt d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((b & d & m).getBoolValue()){
      APInt temp = (b - m) | (m - 1);
      if (temp.uge(a)){
	b = temp;
	break;
      }
      temp = (d - m) | (m - 1);
      if (temp.uge(c)){
	d = temp;
	break;
      }
    }
    m = m.lshr(1);
  }
  return b | d;

}

/// x=[a,b] and y=[c,d] Reduce the value of x & y by increasing the
/// value of a or c and We scan a and c from left to right. If both
/// are 0's then change one to 1 and all subsequent bits to 0. If this
/// value is less or equal than its corresponding upper bound we are
/// done and the result is a & c. If not, we try with the other
/// value. If it doesn't work neither we continue with the scan.
APInt minAnd(APInt a, APInt b, APInt c, APInt d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((~a & ~c & m).getBoolValue()){
      APInt temp = (a | m) &  ~m;
      if (temp.ule(b)){
	a = temp;
	break;
      }
      temp = (c | m) & ~m;
      if (temp.ule(d)){
	c = temp;
	break;
      }
    }
    m = m.lshr(1);
  }
  return a & c;

}

/// x=[a,b] and y=[c,d] Increase the value of x & y by decreasing the
/// value of a or c and We scan b and d from left to right. If one is
/// 0 and the other 1 then change the 1 to 0 and replace the
/// subsequent bits to 1's. If this value is greater or equal than the
/// corresponding lower bound we are done and the result is b & d. If
/// the change cannot be done we try with the other. If not yet, we
/// continue with the scan.
APInt maxAnd(APInt a, APInt b, APInt c, APInt d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((b & ~d & m).getBoolValue()){
      APInt temp = (b & ~m) | (m - 1);
      if (temp.uge(a)){
	b = temp;
	break;
      }
    }
    else{
      if ((~b & d & m).getBoolValue()){
	APInt temp = (d & ~m) | (m - 1);
	if (temp.uge(c)){
	  d = temp;
	  break;
	}
      }
    }
    m = m.lshr(1);
  }
  return b & d;
}


APInt minXor(APInt a, APInt b, APInt c, APInt d){
  return (minAnd(a,b,~d,~c) | minAnd(~b,~a,c,d));
}
APInt maxXor(APInt a, APInt b, APInt c, APInt d){
  return (maxOr(APInt::getNullValue(a.getBitWidth()),
		maxAnd(a,b,~d,~c),
		APInt::getNullValue(a.getBitWidth()),
		maxAnd(~b,~a,c,d)));
}


void BaseRange::unsignedOr(BaseRange *Op1, BaseRange *Op2){
  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   

  setLB(minOr(a,b,c,d));
  setUB(maxOr(a,b,c,c));
 }

void BaseRange::signedOr(BaseRange *Op1, BaseRange*Op2){
   APInt a = Op1->getLB();   
   APInt b = Op1->getUB();
   APInt c = Op2->getLB();   
   APInt d = Op2->getUB();   
   
   unsigned char case_val = 0;
   case_val += (a.isNonNegative() ? 1 : 0);
   case_val <<= 1;
   case_val += (b.isNonNegative() ? 1 : 0);
   case_val <<= 1;
   case_val += (c.isNonNegative() ? 1 : 0);
   case_val <<= 1;
   case_val += (d.isNonNegative() ? 1 : 0);

   APInt lb, ub;
   switch (case_val) {
   case 0:
     lb = minOr(a, b, c, d);
     ub = maxOr(a, b, c, d);
     break;
   case 1:
     lb = a;
     ub = -1;
     break;
   case 3:
     lb = minOr(a, b, c, d);
     ub = maxOr(a, b, c, d);
     break;
   case 4:
     lb = c;
     ub = -1;
     break;
   case 5:
     lb = (a.slt(c) ? a : c);
     ub = maxOr(APInt::getNullValue(a.getBitWidth()), b, APInt::getNullValue(a.getBitWidth()), d);
     break;
   case 7:
     lb = minOr(a, ~APInt::getNullValue(a.getBitWidth()) , c, d);
     ub = minOr(APInt::getNullValue(a.getBitWidth()), b, c, d);
     break;
   case 12:
     lb = minOr(a, b, c, d);
     ub = maxOr(a, b, c, d);
     break;
   case 13:
     lb = minOr(a, b, c, ~APInt::getNullValue(a.getBitWidth()) );
     ub = maxOr(a, b, APInt::getNullValue(a.getBitWidth()), d);
     break;
   case 15:
     lb = minOr(a, b, c, d);
     ub = maxOr(a, b, c, d);
     break;
   default:
     assert(false && "This should not happen");
   }
   setLB(lb);
   setUB(ub);
 }


void BaseRange::unsignedAnd(BaseRange *Op1, BaseRange *Op2){

  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   
  
  setLB(minAnd(a,b,c,d));
  setUB(maxAnd(a,b,c,d));
}

void BaseRange::signedAnd(BaseRange *Op1, BaseRange *Op2){
  // FIXME: do the signed case. This is probably incorrect!
  unsignedAnd(Op1,Op2);
}

void BaseRange::unsignedXor(BaseRange *Op1, BaseRange *Op2){

  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   
  
  setLB(minXor(a,b,c,d));
  setUB(maxXor(a,b,c,d));
}

void BaseRange::signedXor(BaseRange *Op1, BaseRange *Op2){
  // FIXME: do the signed case. This is probably incorrect!
  unsignedXor(Op1,Op2);
}


