// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file  WrappedRange.cpp
///        Wrapped Interval Abstract Domain.
///
/// Many methods have a flag IsSigned. This may be confusing since the
/// analysis is intended to be sign-agnostic. The flag is set in these
/// two cases:
///
/// \li the operation depends on the sign (e.g., comparisons,
///     division, etc).
///
/// \li the operation does not depend on the sign but after we cut at
///     the poles we can then make assumptions about the signs.
///
/// \todo There are many memory leaks: need to fix.
///////////////////////////////////////////////////////////////////////////////

#include "BaseRange.h"
#include "WrappedRange.h"

#include <algorithm>

using namespace llvm;
using namespace unimelb;

// For debugging
//#define DEBUG_FILTER_SIGMA
//#define DEBUG_EVALUATE_GUARD
//#define DEBUG_WIDENING
//#define DEBUG_MEET
//#define DEBUG_JOIN
//#define DEBUG_REFINE_WITH_JUMPS
//#define DEBUG_OVERFLOW_CHECKS
//#define DEBUG_GENERALIZED_JOIN

STATISTIC(NumOfOverflows     ,"Number of overflows");

void printComparisonOp(unsigned Pred,raw_ostream &Out){
  switch(Pred){
  case ICmpInst::ICMP_EQ:  Out<< " = "; break;
  case ICmpInst::ICMP_NE:  Out<< " != ";  break;
  case ICmpInst::ICMP_ULE: Out << " <=_u " ;  break;
  case ICmpInst::ICMP_ULT: Out << " <_u " ;  break;
  case ICmpInst::ICMP_UGT: Out << " >_u " ;  break;
  case ICmpInst::ICMP_UGE: Out << " >=_u " ;  break;
  case ICmpInst::ICMP_SLE: Out << " <=_s " ;  break;
  case ICmpInst::ICMP_SLT: Out << " <_s " ;  break;
  case ICmpInst::ICMP_SGT: Out << " >_s " ;  break;
  case ICmpInst::ICMP_SGE: Out << " >=_s " ;  break;
  default: ;
  }
}

bool WrappedRange::isBot() const { 
  return __isBottom;
}

bool WrappedRange::IsTop() const {  
  return BaseRange::IsTop();
}

void WrappedRange::makeBot(){ 
  __isBottom=true;
  __isTop=false;
}

void WrappedRange::makeTop(){ 
  BaseRange::makeTop();
  __isBottom=false;
}

bool WrappedRange::isEqual(AbstractValue* V){
  // FIXME: identical test is not enough to claim two wrapped ranges
  // are equal. For instance, top have multiple representations
  // [2,1],[1,0], etc. FixpointSSI does not rely on this operation for
  // any vital activity.
  return (BaseRange::isEqual(V));
}

inline bool IsRangeTooBig(APInt lb, APInt ub){
  APInt card  = WrappedRange::WCard(lb,ub);
  // If card does not fit into uint64_t then APInt raises an exception.
  uint64_t n     =  card.getZExtValue();
  // If width of lb and ub are different then APInt raises an exception.
  unsigned width = lb.getBitWidth();
  // If 2^w -1 does not fit into uint64_t then APInt raises an exception.
  uint64_t Max = (APInt::getMaxValue(width)).getZExtValue();
  return (n >= Max);
}

void WrappedRange::convertWidenBoundsToWrappedRange(APInt lb, APInt ub){
  if (IsRangeTooBig(lb,ub))
    makeTop();
  else{
    setLB(lb);
    setUB(ub);
  }
}

void RefinedWithJumpSet(APInt a, APInt b, 
			const SmallPtrSet<ConstantInt*, 16>  JumpSet,
			APInt &lb, APInt &ub){

#ifdef DEBUG_REFINE_WITH_JUMPS
  dbgs() << "Before refinement: \n";
  dbgs() << "LB: " << lb << " UB:" << ub << "\n";
#endif
  // If lb or ub have different widths then APInt raises an exception
  unsigned width = lb.getBitWidth();
  for (SmallPtrSet<ConstantInt*, 16>::iterator I=JumpSet.begin(), 
	 E=JumpSet.end(); I != E; ++I){    
    ConstantInt* C = *I;
    // We can have constants with different bit widths
    if (width == C->getBitWidth()){
      APInt X = C->getValue();      
      if (a.uge(X)) 
	lb = BaseRange::umax(lb,X);
      if (b.ule(X)) {
	ub = BaseRange::umin(ub,X);
      }
    }
  }
#ifdef DEBUG_REFINE_WITH_JUMPS
  dbgs() << "after refinement: \n";
  dbgs() << "LB: " << lb << " UB:" << ub << "\n";
#endif
}

bool checkOverflowForWideningJump(APInt Card){
  // If a or b do not fit into uint64_t or they do not have same width
  // then APInt raises an exception
  uint64_t value = Card.getZExtValue();
  // Max is 2^w/2
  uint64_t Max = (APInt::getMaxValue(Card.getBitWidth() - 1)).getZExtValue();
  return (value >= Max);
}


void WrappedRange::widening(AbstractValue *PreviousV, const SmallPtrSet<ConstantInt*, 16> JumpSet){
	 
  // Make sure that we don't change PreviousV although maybe it's
  // unnecessary
  WrappedRange *Old = cast<WrappedRange>(PreviousV->clone());  
  WrappedRange *New = this;

  // this should not happen but just in case
  if (New->lessOrEqual(Old)) return;

  APInt u = Old->getLB();
  APInt v = Old->getUB();
  APInt x = New->getLB();
  APInt y = New->getUB();

  DEBUG(dbgs() << "\tWIDENING(" );
  DEBUG(Old->printRange(dbgs()));
  DEBUG(dbgs() << "," );
  DEBUG(printRange(dbgs()));
  DEBUG(dbgs() << ")=" );

#ifdef DEBUG_WIDENING
  dbgs() << Old->getValue()->getName() << " ### ";
  dbgs() << "\tWIDENING(" ;
  Old->printRange(dbgs());
  dbgs() << "," ;
  printRange(dbgs());
  dbgs() << ")=" ;
#endif 

  WrappedRange Merged(*Old);
  Merged.join(New);  
  if (Old->lessOrEqual(New) &&  
      (!Old->WrappedMember(x, __SIGNED) && !Old->WrappedMember(y, __SIGNED))) {
#ifdef DEBUG_WIDENING
      dbgs() << "Old value is strictly contained in new value\n";
#endif 
      APInt widen_lb = x;
      APInt cardOld  = WCard(u,v);
      // Overflow check   
      if (checkOverflowForWideningJump(cardOld)){	
	// NumOfOverflows++;
	New->makeTop();
	goto END;	
      }
      APInt widen_ub = umax(x + cardOld + cardOld, y);
      RefinedWithJumpSet(x, y, JumpSet, widen_lb, widen_ub);
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      goto END;
    }
  
  // The next two cases we just check in what direction we are growing
  // and doubling the size of one the intervals.

#ifdef DEBUG_WIDENING
  dbgs() << "Upper bound of old and new value: ";
  Merged.printRange(dbgs());
  dbgs() << "\n";
#endif 
  // We are increasing
  if ( (Merged.getLB() == u) && (Merged.getUB() == y)){
#ifdef DEBUG_WIDENING
    dbgs() << "Widening: the new value is increasing.\n";
#endif 
    APInt cardOld  = WCard(u,v);
    APInt widen_lb = u;
    // Overflow check   
    if (checkOverflowForWideningJump(cardOld)){
      //NumOfOverflows++;
      New->makeTop();
      goto END;	
    }
    APInt widen_ub = umax(u + cardOld + cardOld, y);
#ifdef DEBUG_WIDENING
    dbgs() << "Size of [" << u << "," << v << "]: " << cardOld << "\n";
    dbgs() << "Maximum between " << (u + cardOld + cardOld) << " and " << y << "=" << widen_ub <<"\n";
    dbgs() << "Widen LB: " << widen_lb << "\n";
    dbgs() << "(unsigned) Widen UB: " << widen_ub << "\n";
    dbgs() << "(signed) Widen UB: " << smax(u + cardOld + cardOld, y) << "\n";
#endif 
    RefinedWithJumpSet(x, y, JumpSet, widen_lb, widen_ub);
#ifdef DEBUG_WIDENING
    dbgs() << "After refinment (if any) \n";
    dbgs() << "Widen LB: " << widen_lb << "\n";
    dbgs() << "Widen UB: " << widen_ub << "\n";
#endif 
    New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
    goto END;
  }

  // We are decreasing
  if ( (Merged.getLB() == x) && (Merged.getUB() == v)){
    APInt cardOld  = WCard(u,v);
    // Overflow check   
    if (checkOverflowForWideningJump(cardOld)){
      //NumOfOverflows++;
      New->makeTop();
      goto END;	
    }
    APInt widen_lb = umin(u - cardOld - cardOld, x);
    APInt widen_ub = v;
#ifdef DEBUG_WIDENING
    dbgs() << "Widening: the new value is decreasing.\n";
    dbgs() << "Size of [" << u << "," << v << "]: " << cardOld << "\n";
    dbgs() << "Minimum between " << (u - cardOld - cardOld) << " and " << x << "=" << widen_lb << "\n";
    dbgs() << "Widen LB: " << widen_lb << "\n";
    dbgs() << "Widen UB: " << widen_ub << "\n";
#endif 
    RefinedWithJumpSet(x, y, JumpSet, widen_lb, widen_ub);
#ifdef DEBUG_WIDENING
    dbgs() << "After refinment (if any) \n";
    dbgs() << "Widen LB: " << widen_lb << "\n";
    dbgs() << "Widen UB: " << widen_ub << "\n";
#endif 
    New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
    goto END;
  }
 
  // Otherwise, return old interval
  New->setLB(Old->getLB());
  New->setUB(Old->getUB());

 END: 
  New->normalizeTop();
  DEBUG(printRange(dbgs()));
  DEBUG(dbgs() << "\n");

#ifdef DEBUG_WIDENING
  printRange(dbgs());
  dbgs() << "\n";
#endif

  return;
}

/// Return true if x \in [a,b]. 
bool WrappedRange::WrappedMember(APInt e, bool IsSigned){
  if (isBot()) return false;
  if (IsTop()) return true;

  APInt x = getLB();
  APInt y = getUB();

  // This corresponds to the operation e <=_{x} y in page 7 in the
  // paper. e \in [x,y] iff e <=_{x} y (starting from x we encounter e
  // before than y going clockwise) iff e - x <= y - x

  // dbgs()<< "MEMBERSHIP " << e.toString(10,false) << " in " ;
  // print(dbgs());
  // dbgs() << "\n" << (e - x).ule(y - x) << "\n";
  // dbgs() << ( (x.ule(y) && x.ule(e) && e.ule(y)) ||
  //  	      (x.ugt(y) && (e.ule(x) || y.ule(e)))) << "\n";
  // return (e - x).ule(y - x);


  if (IsSigned){
    return ( (x.sle(y) && x.sle(e) && e.sle(y)) ||
  	     (x.sgt(y) && (e.sle(x) || y.sle(e))));
  }
  else{
    return ( (x.ule(y) && x.ule(e) && e.ule(y)) ||
    	     (x.ugt(y) && (e.ule(x) || y.ule(e))));
  }

}

bool WrappedRange::WrappedlessOrEqual(AbstractValue * V, bool IsSigned){ 
  
  WrappedRange *S = this;
  WrappedRange *T = cast<WrappedRange>(V);  

  // Bottom
  if (S->isBot()) return true;
  // Top
  if (S->IsTop() && T->IsTop()) 
    return true;
  else{
    if (S->IsTop())
      return false;
    else{
      if (T->IsTop()) 
	return true;
    }
  }
  ///
  // a \in T and b \in T and (c \in s and d \in s => s=t)
  ///
  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
  
  return ( T->WrappedMember(a, IsSigned) && 
	   T->WrappedMember(b, IsSigned) &&
	   (S->isEqual(T) || !(S->WrappedMember(c,IsSigned)) || !(S->WrappedMember(d,IsSigned))));	   	    
}


bool WrappedRange::lessOrEqual(AbstractValue * V){ 
  return WrappedlessOrEqual(V, __SIGNED);
}

void WrappedRange::print(raw_ostream &Out) const{
    BaseRange::print(Out);
}

void WrappedRange::join(AbstractValue *V){
  // Join is mostly called when a phi node is encountered. At that
  // point, we cannot make any assumption about signedeness so we need
  // to cut at the south pole
  WrappedRange * R = cast<WrappedRange>(V);

  if (R->isBot()) return;
  if (isBot()){
    WrappedRangeAssign(R); 
    return;
  }

  std::vector<WrappedRange*> s1 = 
    WrappedRange::ssplit(R->getLB(), R->getUB(), R->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    WrappedRange::ssplit(getLB(), getUB(), getLB().getBitWidth());

  for (std::vector<WrappedRange*>::iterator I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){      
      // FIXME: use GeneralizedJoin to get more precise results.
      this->WrappedJoin2((*I1), (*I2));
    }
  }
  normalizeTop();
}

// Just a wrapper.
void WrappedRange::WrappedJoin2(WrappedRange *R1, WrappedRange *R2){
  WrappedJoin(R1, __SIGNED);
  WrappedJoin(R2, __SIGNED);
}

void WrappedRange::WrappedJoin(AbstractValue *V, bool IsSigned){

  WrappedRange *S = this;
  WrappedRange *T = cast<WrappedRange>(V);

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
#ifdef DEBUG_JOIN
  dbgs() << " join( " ;
  S->printRange(dbgs()) ; 
  dbgs() << "," ;
  T->printRange(dbgs()) ; 
  dbgs() << ")=" ;
#endif /*DEBUG_JOIN*/
  // Containment cases (also cover bottom and top cases)
  if (T->WrappedlessOrEqual(S,IsSigned)) {
#ifdef DEBUG_JOIN
    dbgs() << "containment case\n";
#endif 
    goto END;
  }
  if (S->WrappedlessOrEqual(T,IsSigned)) {
#ifdef DEBUG_JOIN
    dbgs() << "containment case\n";
#endif 
    WrappedRangeAssign(T);
    goto END;
  }
  // Extra case for top: one cover the other
  if (T->WrappedMember(a,IsSigned) && T->WrappedMember(b,IsSigned) &&
      S->WrappedMember(c,IsSigned) && S->WrappedMember(d,IsSigned)){
#ifdef DEBUG_JOIN
    dbgs() << "one cover the other case\n";
#endif 
    makeTop();
    goto END;
  }
  // Overlapping cases
  if (S->WrappedMember(c,IsSigned)){
#ifdef DEBUG_JOIN
    dbgs() << "overlapping case\n";
#endif 
    setLB(a);
    setUB(d);
    goto END;
  }
  if (T->WrappedMember(a,IsSigned)){
#ifdef DEBUG_JOIN
    dbgs() << "overlapping case\n";
#endif 
    setLB(c);
    setUB(b);
    goto END;
  }
  // Left/Right Leaning cases: non-deterministic cases

  // Note: since WCard returns cardinalities we can use unsigned
  // comparison here.  
  if (WCard(b,c).ule(WCard(d,a))){
#ifdef DEBUG_JOIN
    dbgs() << "non-overlapping case\n";
#endif 
    setLB(a);
    setUB(d);
    goto END;
  }
  else{
#ifdef DEBUG_JOIN
    dbgs() << "non-overlapping case\n";
#endif 
    setLB(c);
    setUB(b);
    goto END;
  }
 END:
  normalizeTop();

  // This is gross but we need to record that this is not bottom
  // anymore.
  if (!S->isBot() || !T->isBot())
    resetBottomFlag();

#ifdef DEBUG_JOIN
  printRange(dbgs()) ; 
  dbgs() << "\n" ;
#endif 

}


// void test_GeneralizedJoin(){
//   {
//     APInt a(8,  2,false);  APInt b(8, 10,false);
//     APInt c(8,120,false);  APInt d(8,130,false);
//     APInt e(8,132,false);  APInt f(8,135,false);
//     APInt zero(8,0,false); 
//     // Temporary constructors
//     WrappedRange * R1 = new WrappedRange(a,b,a.getBitWidth());
//     WrappedRange * R2 = new WrappedRange(c,d,c.getBitWidth());
//     WrappedRange * R3 = new WrappedRange(e,f,e.getBitWidth());
//     std::vector<WrappedRange*> vv;
//     vv.push_back(R3); vv.push_back(R2); vv.push_back(R1);
//     WrappedRange * Res = new WrappedRange(zero,zero,zero.getBitWidth());  
//     Res->GeneralizedJoin(vv);
//     // it should be [2,135]
//     dbgs()<< "Result for test 1: " ;
//     dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10,false) << "]\n";
//   }

//   {
//     APInt a(8,  2,false);  APInt b(8, 10,false);
//     APInt c(8,120,false);  APInt d(8,130,false);
//     APInt e(8,132,false);  APInt f(8,135,false);
//     APInt g(8,200,false);  APInt h(8,100,false);

//     APInt zero(8,0,false); 
//     // Temporary constructors
//     WrappedRange * R1 = new WrappedRange(a,b,a.getBitWidth());
//     WrappedRange * R2 = new WrappedRange(c,d,c.getBitWidth());
//     WrappedRange * R3 = new WrappedRange(e,f,e.getBitWidth());
//     WrappedRange * R4 = new WrappedRange(g,h,g.getBitWidth());
//     std::vector<WrappedRange*> vv;
//     vv.push_back(R3); vv.push_back(R4); vv.push_back(R2); vv.push_back(R1);
//     WrappedRange * Res = new WrappedRange(zero,zero,zero.getBitWidth());  
//     Res->GeneralizedJoin(vv);
//     // it should be [2,135]
//     dbgs()<< "Result for test 2: " ;
//     dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10,false) << "]\n";
//   }
// }

bool SortWrappedRanges_Compare(WrappedRange *R1, WrappedRange *R2){
  assert(R1);
  assert(R2);
  APInt a = R1->getLB();
  APInt c = R2->getLB();
  return a.ule(c);
}

/// Sort a vector of wrapped ranges in order of lexicographical
/// increasing left bound.
void SortWrappedRanges(std::vector<WrappedRange *> & Rs){
#ifdef DEBUG_GENERALIZED_JOIN
  dbgs() << "before sorted: \n";
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    R->printRange(dbgs());
  }
  dbgs() << "\n";
#endif 
  
  std::sort(Rs.begin(), Rs.end() , SortWrappedRanges_Compare);
  
#ifdef DEBUG_GENERALIZED_JOIN
  dbgs() << "after sorted: \n";
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    R->printRange(dbgs());
  }
  dbgs() << "\n";
#endif 
}

void Extend(WrappedRange * &R1, WrappedRange *R2){  
  R1->join(R2);
}

/// Return the biggest of the two wrapped intervals.
WrappedRange * Bigger(WrappedRange *R1, WrappedRange *R2){

  if (R1->isBot() && !R2->isBot())
    return new WrappedRange(*R2);
  if (R2->isBot() && !R1->isBot())
    return new WrappedRange(*R1);
  if (R2->isBot() && R1->isBot())
    return new WrappedRange(*R1);

  APInt a = R1->getLB();
  APInt b = R1->getUB();
  APInt c = R2->getLB();
  APInt d = R2->getUB();
  if (WrappedRange::WCard(a,b).uge(WrappedRange::WCard(c,d)))
    return new WrappedRange(*R1);
  else 
    return new WrappedRange(*R2);
}

/// If R1 and R2 overlap then return bottom. Otherwise, return the
/// clockwise distance from the end of the first to the start of the
/// second.
WrappedRange * ClockWiseGap(WrappedRange *R1, WrappedRange *R2){
  APInt a = R1->getLB();
  APInt b = R1->getUB();
  APInt c = R2->getLB();
  APInt d = R2->getUB();
  // Temporary constructor!
  WrappedRange * gap = new WrappedRange(b+1,c-1,a.getBitWidth());

  if ( R1->isBot() || R2->isBot() || 
       R2->WrappedMember(b,false) || R1->WrappedMember(c,false)){
    gap->makeBot();
  }
  
  return gap;
}

/// Return true if starting from 0....0 (South Pole) we encounter y
/// before than x.
bool CrossSouthPole(const APInt x,  const APInt y)  {
  return y.ule(x);
}

/// Return true if starting from 2^{w-1} (North Pole) we encounter y
/// before than x.
bool CrossNorthPole(const APInt x,  const APInt y)  {
  APInt max = APInt::getSignedMaxValue(x.getBitWidth());
  // if ((y-max).slt(x-max))
  //   dbgs() << "[" << x.toString(10,false) << "," << y.toString(10,false) << "] is crossing NP.\n";
  return (y-max).slt(x-max);
}

/// Return the complement of a wrapped interval.
WrappedRange* WrappedComplement(WrappedRange *R){
  WrappedRange * C = new WrappedRange(*R);

  if (R->isBot()){
    C->makeTop();
    return C;
  }
  if (R->IsTop()){
    C->makeBot();
    return C;
  }
  
  APInt x = C->getLB();
  APInt y = C->getUB();
  C->setLB(y+1);
  C->setUB(x-1);
  return C;
}

/// Algorithm Fig 3 from the paper. Finding the pseudo least upper
/// bound of a set of wrapped ranges and assign it to this.
void WrappedRange::GeneralizedJoin(std::vector<WrappedRange *> Rs){
  if (Rs.size() < 2) return;

  SortWrappedRanges(Rs);  

  WrappedRange *f = new WrappedRange(*this);
  f->makeBot();

  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    if (R->IsTop() || CrossSouthPole(R->getLB(), R->getUB())){      
#ifdef DEBUG_GENERALIZED_JOIN
      R->printRange(dbgs());
      dbgs() << " crosses the south pole!\n";
      dbgs() << "extend("; 
      f->printRange(dbgs());
      dbgs() << ",";
      R->printRange(dbgs());
      dbgs() << ")=";
#endif 
      Extend(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
      f->printRange(dbgs());
      dbgs() << "\n";
#endif 
    }
  }

  WrappedRange *g = new WrappedRange(*this);
  g->makeBot();
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    WrappedRange *tmp = ClockWiseGap(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
    dbgs() << "gap(";
    f->printRange(dbgs());
    dbgs() << ",";
    R->printRange(dbgs());
    dbgs() << " = ";
    tmp->printRange(dbgs());
    dbgs() << ")\n";

    dbgs() << "Bigger(";
    g->printRange(dbgs());
    dbgs() << ",";
    tmp->printRange(dbgs());
    dbgs() << ") = ";
#endif 
    g = Bigger(g,tmp);
#ifdef DEBUG_GENERALIZED_JOIN
    g->printRange(dbgs());
    dbgs() << "\n";
    dbgs() << "Extend(";
    f->printRange(dbgs());
    dbgs() << ",";
    R->printRange(dbgs());
    dbgs() << ") = ";
#endif 
    Extend(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
      f->printRange(dbgs());
    dbgs() << "\n";
#endif 
  }  
  WrappedComplement(f)->print(dbgs());
  dbgs()<< "\n";
  Bigger(g,WrappedComplement(f))->print(dbgs());
  dbgs()<< "\n";
  WrappedRange *Tmp = WrappedComplement(Bigger(g,WrappedComplement(f)));
  Tmp->print(dbgs());
  dbgs()<< "\n";
  this->setLB(Tmp->getLB());
  this->setUB(Tmp->getUB());
}


void WrappedRange::meet(AbstractValue *V1, AbstractValue *V2){
			
  // FIXME: meet is mostly called when a comparison instruction is
  // encountered. If this is always the case we could call directly to
  // WrappedMeet without cutting at the south pole.
  
  WrappedRange * R1 = cast<WrappedRange>(V1);
  WrappedRange * R2 = cast<WrappedRange>(V2);

  this->makeBot();
  WrappedRange * tmp = new WrappedRange(*this);

  // **SOUTH POLE SPLIT** 
  std::vector<WrappedRange*> s1 = 
    WrappedRange::ssplit(R1->getLB(), R1->getUB(), R1->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    WrappedRange::ssplit(R2->getLB(), R2->getUB(), R2->getLB().getBitWidth());
  for (std::vector<WrappedRange*>::iterator I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){      
      // Note that we need to meet each pair of segments and then join
      // the result of all of them.
      tmp->WrappedMeet((*I1),(*I2), __SIGNED);
      this->WrappedJoin(tmp, __SIGNED);
    }
  }
  delete tmp;
}


void WrappedRange::WrappedMeet(AbstractValue *V1,AbstractValue *V2, bool IsSigned){
  /// 
  //// TEMPORARY
  // test_GeneralizedJoin();
  ////

  // This is gross but we need to turn off the bottom flag. Of course,
  // if the meet returns bottom then the bottom flag will turn on
  // again.
  this->resetBottomFlag();

  assert(!isConstant() && 
	 "The meet method can be only called by a non-constant value");
  WrappedRange *S = cast<WrappedRange>(V1);
  WrappedRange *T = cast<WrappedRange>(V2);

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();

  // Containment cases (also cover bottom and top cases)
  if (S->WrappedlessOrEqual(T,IsSigned)) {
#ifdef DEBUG_MEET
    dbgs() << "Containment case 1\n";
#endif
    WrappedRangeAssign(S);
    goto END;
  }
  if (T->WrappedlessOrEqual(S,IsSigned)) {
#ifdef DEBUG_MEET
    dbgs() << "Containment case 2\n";
#endif
    WrappedRangeAssign(T);
    goto END;
  }
  // If one cover the other the meet is not convex.  We return the one
  //  with smallest cardinality
  if (T->WrappedMember(a,IsSigned) && T->WrappedMember(b,IsSigned) &&
      S->WrappedMember(c,IsSigned) && S->WrappedMember(d,IsSigned)){
#ifdef DEBUG_MEET
    dbgs() << "One cover the other\n";
#endif
    if (WCard(a,b).ule(WCard(c,b))){
      WrappedRangeAssign(S);
      goto END;
    }
    else{
      WrappedRangeAssign(T);
      goto END;
    }
  }
  // Overlapping cases
  if (S->WrappedMember(c,IsSigned)){
#ifdef DEBUG_MEET
    dbgs() << "Overlapping 1\n";
#endif
    setLB(c);
    setUB(b);
    goto END;
  }
  if (T->WrappedMember(a,IsSigned)){
#ifdef DEBUG_MEET
    dbgs() << "Overlapping 2\n";
#endif
    setLB(a);
    setUB(d);
    goto END;
  }
#ifdef DEBUG_MEET
    dbgs() << "Disjoint case\n";
#endif
  // Otherwise, bottom
  makeBot();

 END:
  normalizeTop();
  /*
    DEBUG(dbgs() << "\t" );
    DEBUG(S->printRange(dbgs())) ; 
    DEBUG(dbgs() << " meet " );
    DEBUG(T->printRange(dbgs())) ; 
    DEBUG(dbgs() << " --> " );
    DEBUG(print(dbgs()));
    DEBUG(dbgs() << "\n");    
  */
}

// Comparison operations: these methods are used to tell if the
// evaluation of a guard is true or false.  If return false then it's
// the evaluation of the guard is definite false. If true then we must
// still check the negation of the condition. If also true then the
// evaluation of the guard will be finally "maybe". Otherwise,
// definitely true. 
// Very importantly, these operations depend on the sign. 

/// [a,b] <= [c,d] if a <= d.
inline bool comparisonSle_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <=_s " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().sle(I2->getUB());
}

/// [a,b] < [c,d] if a < d.
inline bool comparisonSlt_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <_s " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().slt(I2->getUB());
}

/// [a,b] <= [c,d] if a <= d.
inline bool comparisonUle_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <=_u " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().ule(I2->getUB());
}

/// [a,b] < [c,d]  if a < d.
inline bool comparisonUlt_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <_u " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().ult(I2->getUB());
}

bool comparisonSignedLessThan(WrappedRange *I1,WrappedRange *I2, bool IsStrict){
  // If IsStrict=true then <= else <
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\t"; 
  I1->printRange(dbgs());
  if (IsStrict) dbgs() << " <_s "; else dbgs() << " <=_s ";    
  I2->printRange(dbgs());
#endif /*DEBUG_EVALUATE_GUARD*/
  // **NORTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<WrappedRange*> s1 = 
    WrappedRange::nsplit(I1->getLB(), I1->getUB(), I1->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    WrappedRange::nsplit(I2->getLB(), I2->getUB(), I2->getLB().getBitWidth());
  bool tmp=false;
  for (std::vector<WrappedRange*>::iterator I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	tmp |= comparisonSlt_SameHemisphere((*I1), (*I2));
      else
	tmp |= comparisonSle_SameHemisphere((*I1), (*I2));
      if (tmp) {
#ifdef DEBUG_EVALUATE_GUARD
	dbgs() <<": true\n";
#endif /*DEBUG_EVALUATE_GUARD*/
	return true; // we dont' bother check all of them if one is already true
      }
    }    
  }
#ifdef DEBUG_EVALUATE_GUARD
  if (tmp) dbgs() <<": true\n";
  else dbgs() <<": false\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return tmp;
}

bool comparisonUnsignedLessThan(WrappedRange *I1, WrappedRange *I2, bool IsStrict){
  // If IsStrict=true then <= else <
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\t"; 
  I1->printRange(dbgs());
  if (IsStrict) dbgs() << " <_u "; else dbgs() << " <=_u ";
  I2->printRange(dbgs());
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  // **SOUTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<WrappedRange*> s1 = 
    WrappedRange::ssplit(I1->getLB(), I1->getUB(), I1->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    WrappedRange::ssplit(I2->getLB(), I2->getUB(), I2->getLB().getBitWidth());

  bool tmp=false;
  for (std::vector<WrappedRange*>::iterator I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	tmp |= comparisonUlt_SameHemisphere((*I1), (*I2));
      else
	tmp |= comparisonUle_SameHemisphere((*I1), (*I2));
      if (tmp){
#ifdef DEBUG_EVALUATE_GUARD
	dbgs() <<": true\n";
#endif /*DEBUG_EVALUATE_GUARD*/
	return true; // we dont' bother check all of them if one is already true
      }
    }    
  }
#ifdef DEBUG_EVALUATE_GUARD
  if (tmp) dbgs() <<": true\n";
  else dbgs() <<": false\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return tmp;
}

bool WrappedRange::comparisonSle(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonSignedLessThan(I1,I2,false);
}

bool WrappedRange::comparisonSlt(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonSignedLessThan(I1,I2,true);
}

bool WrappedRange::comparisonUle(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,false);
}

bool WrappedRange::comparisonUlt(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,true);

}

// Filter methods: they can refine an interval by using information
// from other variables that appear in the guards.

std::vector<std::pair<WrappedRange*,WrappedRange*> > 
keepOnlyFeasibleRanges(unsigned Pred, WrappedRange *V1, WrappedRange *V2){

  std::vector<std::pair<WrappedRange*,WrappedRange*> > res;
  std::vector<WrappedRange*> s1,s2;

  if (BaseRange::IsSignedCompInst(Pred)){
    // **NORTH POLE SPLIT**
    s1 = WrappedRange::nsplit(V1->getLB(), V1->getUB(), V1->getLB().getBitWidth());
    s2 = WrappedRange::nsplit(V2->getLB(), V2->getUB(), V2->getLB().getBitWidth());
  }
  else{
    // **SOUTH POLE SPLIT**
    s1 = WrappedRange::ssplit(V1->getLB(), V1->getUB(), V1->getLB().getBitWidth());
    s2 = WrappedRange::ssplit(V2->getLB(), V2->getUB(), V2->getLB().getBitWidth());
  }
      
  for (std::vector<WrappedRange*>::iterator I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      switch(Pred){
      case ICmpInst::ICMP_EQ:
      case ICmpInst::ICMP_NE:
	// FIMXE: no check??
	res.push_back(std::make_pair((*I1), (*I2)));
        break;
      case ICmpInst::ICMP_SLE:
	if (comparisonSignedLessThan((*I1), (*I2), false))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_SLT:
	if (comparisonSignedLessThan((*I1), (*I2), true))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_ULE:
	if (comparisonUnsignedLessThan((*I1), (*I2), false))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_ULT:
	if (comparisonUnsignedLessThan((*I1), (*I2), true))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;	  
	/////
      case ICmpInst::ICMP_SGT:
	if (comparisonSignedLessThan((*I2), (*I1), true))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_SGE:
	if (comparisonSignedLessThan((*I2), (*I1), false))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_UGT:
	if (comparisonUnsignedLessThan((*I2), (*I1), true))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;
      case ICmpInst::ICMP_UGE:
	if (comparisonUnsignedLessThan((*I2), (*I1), false))
	  res.push_back(std::make_pair((*I1), (*I2)));
	break;

      } // end switch
    } // end inner for
  } //end outer for 

  return res;
}

/// V1 is the range we would like to improve using information from
/// Pred and V2. Therefore, in case we cannot improve we must return
/// V1.
void WrappedRange::filterSigma(unsigned Pred, AbstractValue *V1, AbstractValue *V2){
  WrappedRange *Var1   = cast<WrappedRange>(V1);
  WrappedRange *Var2   = cast<WrappedRange>(V2);
  WrappedRange *Tmp    = new WrappedRange(*this);

#ifdef DEBUG_FILTER_SIGMA
  dbgs() << "Before splitting at north/south poles: " ;
  Var1->printRange(dbgs()); 
  printComparisonOp(Pred,dbgs());    
  Var2->printRange(dbgs()); 
  dbgs() << "\n";      
#endif /*DEBUG_FILTER_SIGMA*/
  
  std::vector<std::pair<WrappedRange*,WrappedRange*> > s =
    keepOnlyFeasibleRanges(Pred,Var1,Var2);

  // During narrowing (this) has a value from the fixpoint computation
  // which we want to (hopefully) improve. This is why we make this bottom. 
  this->makeBot();

  for (std::vector<std::pair<WrappedRange*,WrappedRange*> >::iterator 
	 I=s.begin(), E=s.end(); I!=E; ++I){
#ifdef DEBUG_FILTER_SIGMA
    dbgs() << "After split: \n" ;
#endif /*DEBUG_FILTER_SIGMA*/
    WrappedRange * WI1 = I->first;
    WrappedRange * WI2 = I->second;
#ifdef DEBUG_FILTER_SIGMA
    dbgs() << "\tfiltering pair: (" ;
    WI1->printRange(dbgs()); 
    printComparisonOp(Pred,dbgs());
    WI2->printRange(dbgs()); 
    dbgs() << ")\n";      
#endif /*DEBUG_FILTER_SIGMA*/
    // Note that we have only three cases since I1 is the default
    // value for the sigma node unless it can be improved using I2.
    //
    // Then, if I1 is a constant interval we just return since the
    // interval cannot be further improved.  Otherwise, we have two
    // specialized methods if I2 is also a constant interval or not.
    if (WI1->IsConstantRange()){
      Tmp->WrappedRangeAssign(WI1);
#ifdef DEBUG_FILTER_SIGMA
      dbgs() << "\tNo need of filtering because the interval was already a constant): ";
      Tmp->printRange(dbgs());
      dbgs() << "\n";
#endif /*DEBUG_FILTER_SIGMA*/
      this->WrappedJoin(Tmp,BaseRange::IsSignedCompInst(Pred));      
    }
    else{    
      if (WI2->IsConstantRange()){
	Tmp->filterSigma_VarAndConst(Pred, WI1, WI2);
#ifdef DEBUG_FILTER_SIGMA
	dbgs() << "\tAfter filtering: ";
	Tmp->printRange(dbgs());
	dbgs() << "\n";
#endif /*DEBUG_FILTER_SIGMA*/
	this->WrappedJoin(Tmp,BaseRange::IsSignedCompInst(Pred));
      }
      else{
	Tmp->filterSigma_TwoVars(Pred, WI1, WI2);
#ifdef DEBUG_FILTER_SIGMA
	dbgs() << "\tAfter filtering: ";
	Tmp->printRange(dbgs());
	dbgs() << "\n";
#endif /*DEBUG_FILTER_SIGMA*/
	this->WrappedJoin(Tmp,BaseRange::IsSignedCompInst(Pred));
      }
    }
  } //end for
  this->normalizeTop();    

  delete Tmp;
  return;
}

// FIXME: The code of filterSigma_VarAndConst and filterSigma_TwoVars
// is almost identical to the one in Range. The main difference is in
// the call to meet. We need to factorize code.

/// Special case when one is variable and the other a constant in the
/// branch condition.
void WrappedRange::filterSigma_VarAndConst(unsigned Pred, WrappedRange *V, WrappedRange *N){
  // Assumption: Var is the range we would like to improve using   
  // information from Pred and Const                               
  WrappedRange *LHS = this;
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the meet operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  assert(!V->IsConstantRange() && N->IsConstantRange());
	 
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
      // either the upper bound of V or its lower bound. This case
      // doesn't change wrt to the unwrapped case.
      if (V->getLB() == N->getLB())
	LHS->setLB(V->getLB() + 1);      
      else
	LHS->setLB(V->getLB());

      if (V->getUB() == N->getUB())
	LHS->setUB(V->getUB() - 1);
      else
	LHS->setUB(V->getUB());          

      return;
    }
  case ICmpInst::ICMP_ULE:
  case ICmpInst::ICMP_SLE:
    { /* if v <= n then rng(v) /\ [-oo,n] */      
      // prepare the range [-oo,n]
      // we use signed or unsigned min depending on the instruction
      WrappedRange *TmpRng = new WrappedRange(*N);      
      TmpRng->setLB(getMinValue(Pred)); 	      
      LHS->WrappedMeet(V,TmpRng,IsSignedCompInst(Pred));
      delete TmpRng;
      if (LHS->isBot())
	LHS->WrappedRangeAssign(V);
      return;
    }
  case ICmpInst::ICMP_ULT:	  
  case ICmpInst::ICMP_SLT:	  
    { /* if v < n then rng(v) /\ [-oo,n-1] */
      // prepate the range [-oo,n-1]
      // we use signed or unsigned min depending on the instruction
      WrappedRange *TmpRng = new WrappedRange(*N);      
      TmpRng->setLB(getMinValue(Pred));      
      if (N->getLB() == N->getMinValue()) // to avoid weird things 
	TmpRng->setUB(N->getLB());        // if overflow
      else
	TmpRng->setUB(N->getLB() - 1);   	
      LHS->WrappedMeet(V,TmpRng,IsSignedCompInst(Pred));
      delete TmpRng;
      if (LHS->isBot())
	LHS->WrappedRangeAssign(V);
      return;
    }
  case ICmpInst::ICMP_UGT:
  case ICmpInst::ICMP_SGT:
    { /* if v > n then  rng(v) /\ [n+1,+oo] */ 
      // prepare range [n+1,+oo]
      // we use signed or unsigned max depending on the instruction
      WrappedRange *TmpRng = new WrappedRange(*N);
      TmpRng->setUB(getMaxValue(Pred));
      if (N->getUB() == N->getMaxValue()) // to avoid weird things 
        TmpRng->setLB(N->getUB());        // if overflow
      else
	TmpRng->setLB(N->getUB() + 1);       
      LHS->WrappedMeet(V,TmpRng,IsSignedCompInst(Pred));
      delete TmpRng;
      if (LHS->isBot())
	LHS->WrappedRangeAssign(V);
      return;
    }    
  case ICmpInst::ICMP_UGE:
  case ICmpInst::ICMP_SGE:
    { /* if v >= n then  rng(v) /\ [n,+oo] */ 
      // prepare the range [n,+oo]
      // we use signed or unsigned max depending on the instruction
      WrappedRange *TmpRng = new WrappedRange(*N);
      TmpRng->setLB(N->getUB()); 
      TmpRng->setUB(getMaxValue(Pred)); 
      LHS->WrappedMeet(V,TmpRng,IsSignedCompInst(Pred));
      delete TmpRng;
      if (LHS->isBot())
	LHS->WrappedRangeAssign(V);
      return;
    }  
  default:
    assert(false && "unexpected error in filterSigma_VarAndConst");
  }
}

/// The condition of the branch involves two variables.
void WrappedRange::filterSigma_TwoVars(unsigned Pred, 
				       WrappedRange *I1, WrappedRange *I2){

  // Assumption: V1 is the range we would like to improve using
  // information from Pred and V2
  WrappedRange *LHS  = this;  
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the meet operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  assert(!I1->IsConstantRange() &&  !I2->IsConstantRange());

  // Special cases first
  if (I2->isBot()){ 
    // If I2 is bottom, we dont' have chance to improve I1
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  }

  ///// KEY OPERATION and difference wrt to Range class.
  LHS->WrappedMeet(I1,I2,IsSignedCompInst(Pred));

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
    if (BaseRange::bridge_IsIncluded(Pred,I2->getLB(),I2->getUB(),I1->getLB(),I1->getUB())){
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
    if (BaseRange::bridge_IsOverlapLeft(Pred,I1->getLB(),I1->getUB(),I2->getLB(),I2->getUB())){
      // The result is the meet between I1 and I2
      return;
    }     
    // Otherwise, no improvement. That is, overlap-right or I1
    // included in I2 cannot improve our knowledge about I1
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  case ICmpInst::ICMP_UGT: 
  case ICmpInst::ICMP_UGE: 
  case ICmpInst::ICMP_SGT: 
  case ICmpInst::ICMP_SGE: 
    if (BaseRange::bridge_IsIncluded(Pred,I2->getLB(),I2->getUB(),I1->getLB(),I1->getUB())){
      ////////////////////////////////////////////////////////////////////////////
      // Case where we can improve further the meet
      ////////////////////////////////////////////////////////////////////////////
      // E.g., [-10,+oo] >= [-5,-2] --> [-5,+oo]
      // E.g., [-10,+oo] >  [-5,-2] --> [-4,+oo]
      LHS->setUB(I1->getUB());
      if (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_UGE)
	LHS->setLB(I2->getLB());
      else
	LHS->setLB(I2->getLB()+1);	
      return;
    }
    if (BaseRange::bridge_IsOverlapRight(Pred,I1->getLB(),I1->getUB(),I2->getLB(),I2->getUB())){
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

// Begin overflow checks  for arithmetic operations

/// Return true iff overflow during addition or substraction (same
/// condition).
bool IsWrappedOverflow_AddSub(APInt a, APInt b, APInt c, APInt d){
  // a,b,c,d are unsigned 
  //
  // If the four APInt's do not have the same width then APInt raises
  // an exception.
  unsigned width = a.getBitWidth();
  APInt tmp1  = WrappedRange::WCard(a,b);  
  APInt tmp2  = WrappedRange::WCard(c,d);  
  // If tmp1 or tmp2 do not fit into uint64_t then APInt raises an
  // exception.
  uint64_t n1  =  tmp1.getZExtValue();
  uint64_t n2  =  tmp2.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(width)).getZExtValue();
#ifdef DEBUG_OVERFLOW_CHECKS
  dbgs() << "\nOverflow test: " << n1 << "+" << n2 << " >= " << Max << "\n";
#endif
  return ((n1 + n2) > Max);
}

/// return true iff overflow during truncation.
bool IsWrappedOverflow_Trunc(WrappedRange * RHS, unsigned destWidth){
  APInt a = RHS->getLB();
  APInt b = RHS->getUB();
  APInt tmp  = WrappedRange::WCard(a,b);
  // If tmp does not fit into uint64_t then APInt raises an exception.
  uint64_t n   =  tmp.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(destWidth)).getZExtValue();
  return (n > Max);
}


/// Return true iff overflow during left shift.
bool IsWrappedOverflow_Shl(WrappedRange * Op, APInt shift){
  APInt a = Op->getLB();
  APInt b = Op->getUB();
  APInt tmp  = WrappedRange::WCard(a,b);
  // If tmp does not fit into uint64_t then APInt raises an exception.
  uint64_t n   =  tmp.getZExtValue() << shift.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(a.getBitWidth())).getZExtValue();
  return (n > Max);
}

/// Do some preparation for testing overflow

void promoteAPIntToRawInt(APInt a, APInt b, APInt c, APInt d,
			  // APInt's promoted to uint64_t's
			  uint64_t &na, uint64_t &nb, uint64_t &nc, uint64_t &nd,
			  // Max for overflow checks
			  uint64_t &Max){
  // If a,b,c,or d do not fit into uint64_t or they do not have same
  // width then APInt raises an exception
  na = a.getZExtValue();
  nb = b.getZExtValue();
  nc = c.getZExtValue();
  nd = d.getZExtValue();
  unsigned width = a.getBitWidth();
  Max = (APInt::getMaxValue(width)).getZExtValue();
}

// End overflow checks  for arithmetic operations

// Begin machinery for arithmetic and bitwise operations

std::vector<WrappedRange*> WrappedRange::nsplit(APInt x, APInt y, unsigned width){
  // Temporary wrapped interval for north pole
  APInt NP_lb = APInt::getSignedMaxValue(width); // 0111...1
  APInt NP_ub = APInt::getSignedMinValue(width); // 1000...0
  WrappedRange *NP = new WrappedRange(NP_lb,NP_ub,width);
  // Temporary wrapped interval 
  WrappedRange *s  = new WrappedRange(x,y,width);

  std::vector<WrappedRange*> res;
  if (s->WrappedlessOrEqual(NP, true)){
    ///                         ^^^^ signed
    // No need of split
    res.push_back(s);
    // dbgs() << "No split for: " << "[" << x << "," << y << "]" << "\n ";  

    // delete NP;
    return res;
  }
  // dbgs() << "Splitting:" << "[" << x << "," << y << "]" << " into:\n ";  
  // Split into two wrapped intervals
  WrappedRange *s1  = new WrappedRange(x,NP_lb,width); // [x,  0111...1]
  WrappedRange *s2  = new WrappedRange(NP_ub,y,width); // [1000....0, y]

  /*
    s1->printRange(dbgs());
    dbgs() << " and ";
    s2->printRange(dbgs());
    dbgs() << "\n";
  */

  res.push_back(s1);
  res.push_back(s2);

  // delete NP;
  // delete s;  
  return res;  
}

std::vector<WrappedRange*> WrappedRange::ssplit(APInt x, APInt y, unsigned width){
  // Temporary wrapped interval for south pole
  APInt SP_lb(width,-1,false);          // 111...1
  //                    ^^^^^ unsigned  // 000...0
  APInt SP_ub(width, 0,false);
  //                    ^^^^^ unsigned
  WrappedRange *SP = new WrappedRange(SP_lb,SP_ub,width);
  // Temporary wrapped interval 
  WrappedRange *s  = new WrappedRange(x,y,width);

  std::vector<WrappedRange*> res;
  if (s->WrappedlessOrEqual(SP,false)){
    //                         ^^^^^ unsigned
    // No need of split
    res.push_back(s);

    //  delete SP;
    return res;
  }
  
  // Split into two wrapped intervals
  WrappedRange *s1  = new WrappedRange(x,SP_lb,width); // [x, 111....1]
  WrappedRange *s2  = new WrappedRange(SP_ub,y,width); // [000...0,  y] 
  res.push_back(s1);
  res.push_back(s2);

  //delete SP;
  //delete s;
  return res;  
}


std::vector<WrappedRange*> psplit(APInt x, APInt y, unsigned width){

  std::vector<WrappedRange*> res;  
  std::vector<WrappedRange*> s1 = WrappedRange::nsplit(x,y,width);

  for (std::vector<WrappedRange*>::iterator I = s1.begin(),
	 E=s1.end() ; I!=E ; ++I){
    WrappedRange *r = *I;
    std::vector<WrappedRange*> s2  = 
      WrappedRange::ssplit(r->getLB(),r->getUB(),r->getLB().getBitWidth());
    // append all elements of s2 into res
    res.insert(res.end(),s2.begin(),s2.end());
  }
  return res;
}

// End machinery for arithmetic and bitwise operations


void UnsignedWrappedMult(WrappedRange *LHS,
			 WrappedRange *Op1, WrappedRange *Op2){

  uint64_t na,nb,nc,nd,Max;
  promoteAPIntToRawInt(Op1->getLB(),Op1->getUB(),Op2->getLB(),Op2->getUB(),
		       na,nb,nc,nd,Max);

  if ((nb*nd) - (na*nc) > Max){
    NumOfOverflows++;
    LHS->makeTop();
    return;
  }	
  LHS->setLB(Op1->getLB() * Op2->getLB());
  LHS->setUB(Op1->getUB() * Op2->getUB());
  return;  
}


/// When we say positive or negative we simply means if the MSB is 1
/// or 0. We rely on APInt::isNegative to return true if the high bit
/// of the APInt is set.
bool AllSameSign(APInt a, APInt b, APInt c, APInt d){
  bool AllNeg = (a.isNegative()    && b.isNegative()    && c.isNegative()    && d.isNegative());
  bool AllPos = (a.isNonNegative() && b.isNonNegative() && c.isNonNegative() && d.isNonNegative());
  return (AllNeg || AllPos);
}

bool HasNegPos(APInt a, APInt b, APInt c, APInt d){
  return ((a.isNegative() && b.isNegative()) 
	  &&
	  (c.isNonNegative() && d.isNonNegative()) );
}

bool HasPosNeg(APInt a, APInt b, APInt c, APInt d){
  return ((a.isNonNegative() && b.isNonNegative()) 
	  &&
	  (c.isNegative() && d.isNegative()) );
}


void SignedWrappedMult(WrappedRange *LHS,
		       WrappedRange *Op1, WrappedRange *Op2){
  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();

  if (AllSameSign(a,b,c,d)){
    // Overflow check is done by UnsignedWrappedMult
    return UnsignedWrappedMult(LHS,Op1,Op2);
  }

  uint64_t na,nb,nc,nd,Max;
  promoteAPIntToRawInt(Op1->getLB(),Op1->getUB(),Op2->getLB(),Op2->getUB(),
		       na,nb,nc,nd,Max);

  if (HasNegPos(a,b,c,d) && ((nb*nc) - (na*nd) <= Max)){
    LHS->setLB(a*d);
    LHS->setUB(b*c);    
    return;
  }

  if (HasPosNeg(a,b,c,d) && ((na*nd) - (nb*nc) <= Max)){
    LHS->setLB(b*c);
    LHS->setUB(a*d);    
    return;
  }

  NumOfOverflows++;  
  LHS->makeTop();
}

void SignedUnsignedWrappedMult(WrappedRange *Res,	
			       WrappedRange *Op1, WrappedRange *Op2){
  WrappedRange *Tmp1 = new WrappedRange(*Res);
  WrappedRange *Tmp2 = new WrappedRange(*Res);
  UnsignedWrappedMult(Tmp1,Op1,Op2);
  SignedWrappedMult(Tmp2,Op1,Op2);
  Res->WrappedMeet(Tmp1,Tmp2, __SIGNED);

  //delete Tmp1;
  //delete Tmp2;      
}
    
void WrappedRange::WrappedMultiplication(WrappedRange *LHS, 
					 WrappedRange *Op1,WrappedRange *Op2){
  // Trivial case
  if (Op1->IsZeroRange() || Op2->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    return;
  }
  
  // General case: south pole split and north pole split (signed) and
  // compute operation for each element of the Cartesian product and
  // then lubbing them
  std::vector<WrappedRange*> s1 = 
    psplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    psplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth());
  WrappedRange * Tmp = new WrappedRange(*LHS);
  LHS->makeBot();  
  for (std::vector<WrappedRange*>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      SignedUnsignedWrappedMult(Tmp,*I1,*I2);
      // TODO: better call to GeneralizedJoin with all Tmps's
      LHS->join(Tmp);
    }
  }

  // delete Tmp;
}

void WrappedRange::WrappedDivisionAndRem(unsigned Opcode,
					 WrappedRange *LHS, 
					 WrappedRange *Dividend, WrappedRange *Divisor, 
					 bool IsSigned){

  assert(!Divisor->IsZeroRange() && "ERROR: division by zero!");

  // Trivial case
  if (Dividend->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    //   LHS->setWrapped(false);
    return;
  }
  
  // General case: south pole split (unsigned) and north pole split
  // (signed) and compute operation for each element of the Cartesian
  // product and then lubbing them

  if (IsSigned){
    std::vector<WrappedRange*> s1 = 
      nsplit(Dividend->getLB(), Dividend->getUB(), Dividend->getLB().getBitWidth());
    std::vector<WrappedRange*> s2 = 
      nsplit(Divisor->getLB(), Divisor->getUB(), Divisor->getLB().getBitWidth());

    WrappedRange * Tmp = new WrappedRange(*LHS);
    LHS->makeBot();  
    for (std::vector<WrappedRange*>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (std::vector<WrappedRange*>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	// Defined in BaseRange
	bool IsOverflow;
	DivRem_GeneralCase(Opcode,Tmp,*I1,*I2,IsOverflow);
	if (IsOverflow){
	  NumOfOverflows++;
	  LHS->makeTop();
	  break;
	}
	LHS->join(Tmp);
      }
    }

    //delete Tmp;
  }
  else{
    std::vector<WrappedRange*> s1 = 
      ssplit(Dividend->getLB(), Dividend->getUB(), Dividend->getLB().getBitWidth());
    std::vector<WrappedRange*> s2 = 
      ssplit(Divisor->getLB(), Divisor->getUB(), Divisor->getLB().getBitWidth());

    WrappedRange * Tmp = new WrappedRange(*LHS);
    LHS->makeBot();  
    for (std::vector<WrappedRange*>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (std::vector<WrappedRange*>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	// Defined in BaseRange
	//(*I1)->printRange(dbgs()) ; dbgs() << " urem ";
	//(*I2)->printRange(dbgs()) ; dbgs() << " = ";	
	UDivRem_GeneralCase(Opcode,Tmp,*I1,*I2);
	//Tmp->printRange(dbgs()); dbgs() << "\n";
	LHS->join(Tmp);
      }
    }

    //delete Tmp;
  }
}


/// Perform the transfer function for binary arithmetic operations.
AbstractValue* WrappedRange::visitArithBinaryOp(AbstractValue *V1,AbstractValue *V2,
						unsigned OpCode, const char *OpCodeName){
  
  WrappedRange *Op1 = cast<WrappedRange>(V1);
  WrappedRange *Op2 = cast<WrappedRange>(V2);
  WrappedRange *LHS = new WrappedRange(*this);
        
  DEBUG(dbgs() << "\t [RESULT] ");
  DEBUG(Op1->printRange(dbgs()));
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs()));
  DEBUG(dbgs() << " = ");

  /// First simple cases: bottom, top, etc
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeBot();
    goto END;
  }
  if (Op1->IsTop() || Op2->IsTop()){
    LHS->makeTop();
    goto END;
  }
  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the arithmetic operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  switch (OpCode){
  case Instruction::Add:
  case Instruction::Sub:
    //  [a,b] + [c,d] = [a+c,b+d] if Add and no overflow
    //  [a,b] - [c,d] = [a-d,b-c] if Sub and no overflow
    //  top                       otherwise
    if (IsWrappedOverflow_AddSub(Op1->getLB(),Op1->getUB(),Op2->getLB(),Op2->getUB())){
      NumOfOverflows++;
      LHS->makeTop();
      goto END;
    }
    
    if (OpCode == Instruction::Add){
      // Addition in APInt performs modular arithmetic
      LHS->setLB(Op1->getLB() + Op2->getLB());
      LHS->setUB(Op1->getUB() + Op2->getUB());
    }
    else{
      /// Substraction in APInt performs modular arithmetic
      LHS->setLB(Op1->getLB() - Op2->getUB());
      LHS->setUB(Op1->getUB() - Op2->getLB());
    }      
    break;
  case Instruction::Mul:
    WrappedMultiplication(LHS, Op1, Op2);
    break;
  case Instruction::UDiv:
  case Instruction::URem:
    WrappedDivisionAndRem(OpCode, LHS, Op1,Op2, false);
    break;
  case Instruction::SRem:
  case Instruction::SDiv:
    WrappedDivisionAndRem(OpCode, LHS, Op1, Op2, true);
    break;
  default:
    dbgs() << OpCodeName << "\n";
    assert(false && "Arithmetic operation not implemented");
  } // end switch

 END:
  LHS->normalizeTop();
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");              
  return LHS;
}

// We factorize code here because truncation and shift on the left use
// this operation.
bool Truncate(WrappedRange *&LHS, WrappedRange *Operand, unsigned k){

  if (IsWrappedOverflow_Trunc(Operand,k)){
    NumOfOverflows++;
    LHS->makeTop();
    return true;
  }

  APInt a= Operand->getLB();
  APInt b= Operand->getUB();
  assert(a.getBitWidth() == b.getBitWidth());

  //dbgs() << "Truncate to " << k << " bits.\n";
  //dbgs() << "Width of a and b are: " << a.getBitWidth() << " and " << b.getBitWidth() << "\n";

  if (k == a.getBitWidth()) return false;

  // Not sure this is correct. It's different from the paper.
  // We need to check if RHS->getUB() and RHS->getLB() agree on
  // the most significant k bits. (Look at the paper for this)
  LHS->setLB(a.trunc(k)); 	  
  LHS->setUB(b.trunc(k)); 
  return true;
}
 
/// Perform the transfer function for casting operations.
AbstractValue* WrappedRange::visitCast(Instruction &I, 
				       AbstractValue * V, TBool *TB, bool){

  // Very special case: convert TBool to WrappedRange
  WrappedRange *RHS = NULL;
  if (!V){
    // Special case if the source is a Boolean Flag    
    assert(TB && "ERROR: visitCat assumes that TB != NULL");
    RHS = new WrappedRange(I.getOperand(0), TB);
  }
  else{
    // Common case
    RHS = cast<WrappedRange>(V);    
    assert(!TB && "ERROR: some inconsistency found in visitCast");
  }
  WrappedRange *LHS = new WrappedRange(*this);

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the casting operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  // Check some possible errors
  unsigned srcWidth,destWidth;  
  const Type * srcTy  =  I.getOperand(0)->getType();
  const Type * destTy =  I.getType();
  BaseRange::checkCastingOp(srcTy, srcWidth, destTy, destWidth,I.getOpcode(),RHS->getWidth());
  
  /// Start doing casting: change width
  LHS->setWidth(destWidth);        
  
  /// Simple cases first: bottom and top
  if (RHS->isBot()){
    LHS->makeTop(); // be conservative
    goto END;
  }    
  if (RHS->IsTop()){
    LHS->makeTop();
    goto END;
  }
  
  switch(I.getOpcode()) {
  case Instruction::Trunc:
    {
      unsigned k;
      Utilities::getIntegerWidth(I.getType(),k);      
      Truncate(LHS, RHS,k);
    }
    break;
  case Instruction::ZExt:
    {
      unsigned k;
      Utilities::getIntegerWidth(I.getType(),k);
      // **SOUTH POLE SPLIT** and compute signed extension for each of
      // two elements and then lubbing them
      std::vector<WrappedRange*> s = 
	ssplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth());
      WrappedRange * Tmp = new WrappedRange(*LHS);
      LHS->makeBot();  
      for (std::vector<WrappedRange*>::iterator I=s.begin(), E=s.end(); I!=E; ++I){
	APInt a = (*I)->getLB();
	APInt b = (*I)->getUB();
	Tmp->setLB(a.sext(k));
	Tmp->setUB(b.sext(k));    
	// FIXME: we could use here GeneralizedJoin for more precision
	LHS->join(Tmp);
      }
    }
    break;
  case Instruction::SExt:  
    {  
      unsigned k;
      Utilities::getIntegerWidth(I.getType(),k);
      // **NORTH POLE SPLIT** and compute signed extension for each of
      // the two elements and then lubbing them
      std::vector<WrappedRange*> s = 
	nsplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth());
      WrappedRange * Tmp = new WrappedRange(*LHS);
      LHS->makeBot();  
      for (std::vector<WrappedRange*>::iterator I=s.begin(), E=s.end(); I!=E; ++I){
	APInt a = (*I)->getLB();
	APInt b = (*I)->getUB();
	Tmp->setLB(a.sext(k));
	Tmp->setUB(b.sext(k));    
	// FIXME: we could use here GeneralizedJoin for more precision
	LHS->join(Tmp);
      }
    }
    break;    
  default:; // bitcast are non-op
    } // end switch
  
 END:
  LHS->normalizeTop();    
  // if (!V)
  //   delete RHS;
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");      
  return LHS;
}

void WrappedRange::WrappedLogicalBitwise(WrappedRange *LHS, 
					 WrappedRange *Op1, WrappedRange *Op2,
					 unsigned Opcode){
 
  // General case: **SOUTH POLE SPLIT** and compute operation for each
  // of the elements and then lubbing them

  std::vector<WrappedRange*> s1 = 
    ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth());
  std::vector<WrappedRange*> s2 = 
    ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth());
  WrappedRange * Tmp = new WrappedRange(*LHS);
  LHS->makeBot();  
  for (std::vector<WrappedRange*>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (std::vector<WrappedRange*>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      switch(Opcode){
      case Instruction::Or:
	//(*I1)->printRange(dbgs()); dbgs() << " or ";
	//(*I2)->printRange(dbgs()); dbgs() << " = ";

	// TODO: more base cases
	if ((*I1)->IsZeroRange()){
	  Tmp->RangeAssign((*I2));
	}
	else if ((*I2)->IsZeroRange()){
	  Tmp->RangeAssign((*I1));
	}
	else
	  Tmp->unsignedOr(*I1,*I2);
	//Tmp->printRange(dbgs()); dbgs() << "\n";
	break;
      case Instruction::And:
	//(*I1)->printRange(dbgs()); dbgs() << " and ";
	//(*I2)->printRange(dbgs()); dbgs() << " = ";

	if ((*I1)->IsZeroRange())
	  Tmp->RangeAssign((*I1));
	else if ((*I2)->IsZeroRange())
	  Tmp->RangeAssign((*I2));
	else
	  Tmp->unsignedAnd(*I1,*I2);
	//Tmp->printRange(dbgs()); dbgs() << "\n";
	break;
      case Instruction::Xor:
	//(*I1)->printRange(dbgs()); dbgs() << " xor ";
	//(*I2)->printRange(dbgs()); dbgs() << " = ";
	Tmp->unsignedXor(*I1,*I2);
	//Tmp->printRange(dbgs()); dbgs() << "\n";
	break;
      default:
	assert(false && "Unexpected instruction");
      } // end switch
      // FIXME: we could use GeneralizedJoin to be more precise.
      LHS->join(Tmp);
    }
  }
  //dbgs() << "After lubbing "; LHS->print(dbgs()); dbgs() << "\n";
  delete Tmp;
}


void WrappedRange::WrappedBitwiseShifts(WrappedRange *LHS, 
					WrappedRange *Operand, WrappedRange *Shift,
					unsigned Opcode){

  switch(Opcode){
  case Instruction::Shl:    
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      unsigned NumBitsSurviveShift = k.getBitWidth() - k.getZExtValue();
      WrappedRange * Tmp = new WrappedRange(*Operand);
      Truncate(Tmp, Operand, NumBitsSurviveShift);
      // Be careful: truncate will reduce the width of Tmp.  To
      // compare with a and b we need to pad 0's so that all of them
      // have the same width again.
      APInt Tmp_lb(k.getBitWidth(), Tmp->getLB().getZExtValue(), false);
      APInt Tmp_ub(k.getBitWidth(), Tmp->getUB().getZExtValue(), false);
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();
      assert(Tmp_lb.getBitWidth() == a.getBitWidth() && 
	     Tmp_ub.getBitWidth() == b.getBitWidth());
      //dbgs() << Tmp_lb << " -- " << Tmp_ub << " --- " << a << " --- " << b << "\n";
      if (!Tmp->isBot() && !Tmp->IsTop() && (Tmp_lb == a) && (Tmp_ub == b)){
	// At this point the shift will not through away relevant bits
	// so it is safe to shift on the left.
	LHS->setLB(a << k);
	LHS->setUB(b << k);    
      }
      else{
	// 000.......0
	LHS->setLB(APInt::getNullValue(a.getBitWidth())); 
	// 1111...0000 where the number of 1's is w-k.
	LHS->setUB(APInt::getHighBitsSet(a.getBitWidth(), NumBitsSurviveShift-1));  
      }
      delete Tmp;
    }
    else{
      // FIXME: NOT_IMPLEMENTED if the shift cannot be inferred as a
      // constant at compile time
      LHS->makeTop();
    }
    break;
  case Instruction::LShr:
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();	
      /// If SOUTH POLE \in [a,b] then [0^w, 0^k 1^{w-k}]  (rule 1) 
      /// otherwise [ a >>_l k, b >>_l k]                   (rule 2)
      ///
      /// The range crosses the south pole.  E.g., if we shift
      /// logically two bits each bound of the range [0011,0001] to
      /// the right we would get [0000,0000]. However, assume that the
      /// exact value is 1111 (which is included in that range) and
      /// shift logically two bits to the right. We would get 0011 !
      /// To cover this case we have rule 1.
      if (Operand->IsTop() || CrossSouthPole(a,b)){
	// 0.......0
	LHS->setLB(APInt::getNullValue(a.getBitWidth()));
	// 0..01...1 where the number of 1's is width-k
	LHS->setUB(APInt::getLowBitsSet(a.getBitWidth(), a.getBitWidth() - k.getZExtValue())); 
      }
      else{
	LHS->setLB(a.lshr(k));
	LHS->setUB(b.lshr(k));    
      }
    }
    else{
      // FIXME: NOT_IMPLEMENTED if shift cannot be inferred as a
      // constant at compile time.
      LHS->makeTop();
    }
    break;
  case Instruction::AShr:
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();	
      /// If NORTH POLE \in [a,b] then [1^{k}0^{w-k}, 0^k 1^{w-k}]  (rule 1) 
      /// otherwise [ a >>_a k, b >>_a k]                           (rule 2)
      ///
      if (Operand->IsTop() || CrossNorthPole(a,b)){
	// lower bound is 1...10....0 where the number of 1's is k.
	LHS->setLB(APInt::getHighBitsSet(a.getBitWidth(), k.getZExtValue()));  
	// upper bound is 0..01...1 where the number of 1's is width-k
	LHS->setUB(APInt::getLowBitsSet(b.getBitWidth(), b.getBitWidth() - k.getZExtValue()));    
      }
      else{
	LHS->setLB(a.ashr(k));
	LHS->setUB(b.ashr(k));    
      }
    }
    else{
      // FIXME: NOT_IMPLEMENTED if shift cannot be inferred as a
      // constant at compile time.
      LHS->makeTop();
    }
    break;
  default:
    assert(false && "Unexpected instruction");
  } // end switch
}


/// Perform the transfer function for bitwise  operations. 
AbstractValue* WrappedRange::visitBitwiseBinaryOp(AbstractValue * V1, 
						  AbstractValue * V2, 
						  const Type * Op1Ty, const Type * Op2Ty, 
						  unsigned OpCode   , const char * OpCodeName){

  WrappedRange *Op1 = cast<WrappedRange>(V1);
  WrappedRange *Op2 = cast<WrappedRange>(V2);
  WrappedRange *LHS = new WrappedRange(*this);

  // Be careful: top can be improved. Therefore, don't return directly
  // top if one of the operand is top

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the bitwise operation returns bottom then the bottom
  // flag will turn on again.
  LHS->resetBottomFlag();

  switch(OpCode){
  case Instruction::And:
  case Instruction::Xor:
  case Instruction::Or:
    if (Op1->isBot() || Op2->isBot()){
      LHS->makeBot();
      break;
    }
    /////////////////////////////////////////////////////////////////
    // Top is special for logical bitwise because we can go down in
    // the lattice from it.
    /////////////////////////////////////////////////////////////////
    if (Op1->IsTop() && Op2->IsTop()){
      LHS->makeTop();
      break;
    }      
    if (Op1->IsTop()){
      WrappedRange* Tmp = new WrappedRange(*Op1);
      Tmp->resetTopFlag();

      Tmp->setLB((uint64_t) 0);
      Tmp->setUB(APInt::getMaxValue(Tmp->getWidth()));
      WrappedLogicalBitwise(LHS, Tmp, Op2, OpCode);	  
      delete Tmp;
      break;
    }      
    if (Op2->IsTop()){
      WrappedRange* Tmp = new WrappedRange(*Op2);
      Tmp->resetTopFlag();

      Tmp->setLB((uint64_t) 0);
      Tmp->setUB(APInt::getMaxValue(Tmp->getWidth()));
      WrappedLogicalBitwise(LHS, Op1, Tmp,  OpCode);	  
      delete Tmp;
      break;
    }      
    WrappedLogicalBitwise(LHS, Op1, Op2, OpCode);
    break;
  case Instruction::Shl: 
  case Instruction::LShr: 
  case Instruction::AShr: 
    if (Op1->isBot() || Op2->isBot()){ //be conservative here
      LHS->makeTop();
      break;
    }

    if (!checkOpWithShift(Op1,Op2)){
      LHS->makeTop();
      break;
    }

    WrappedBitwiseShifts(LHS, Op1, Op2,OpCode);
    break;
  default:;
  } // end switch

  LHS->normalizeTop();    
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");        
  return LHS;  
}



				

