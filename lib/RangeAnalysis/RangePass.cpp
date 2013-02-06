// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file RangeVariableAnalyses.cpp
///       Range Integer Variable Passes.
//////////////////////////////////////////////////////////////////////////////

#include "FixpointSSI.h"
#include "Transformations/vSSA.h"
#include "Range.h"
#include "WrappedRange.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Module.h"
#include "llvm/Value.h"
#include "llvm/Instructions.h"
#include "llvm/ValueSymbolTable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;
using namespace unimelb;

cl::opt<unsigned>  widening("widening",
			     cl::init(3),
			     cl::Hidden,
		             cl::desc("Widening threshold (0: no widening)")); //!< User option to choose widening threshold.

cl::opt<unsigned>  narrowing("narrowing",
			     cl::init(1),
			     cl::Hidden,
		             cl::desc("Narrowing iterations (0: no narrowing)")); //!< User option to choose narrowing.

cl::opt<bool> enableOptimizations("enable-optimizations", 
				  cl::Hidden,
				  cl::desc("Enable LLVM optimizations (default = false)"),
				  cl::init(false)); //!< User option to run LLVM optimizations.

cl::opt<bool> instCombine("InstCombine", 
			  cl::Hidden,
			  cl::desc("Enable -instcombine LLVM pass (default = false)"),
			  cl::init(false)); //!< User option to run -instcombine.

cl::opt<unsigned> Inline("Inline", 
			 cl::init(0),
			 cl::Hidden,
			 cl::desc("Enable inlining of functions (default = 0)")); //!< User option to inline functions.
		     
// For range analysis
#define SIGNED_RANGE_ANALYSIS true
// For printing more information
#define MORE_COMPARISON_DETAILS
// For printing analysis results
#define PRINT_RESULTS

namespace unimelb {

  /// An utility function that adds a pass to the pass manager.
  inline void addPass(PassManager &PM, Pass *P) {
    // Add the pass to the pass manager...
    PM.add(P);  
    dbgs() << "[RangeAnalysis]: running pass " <<  P->getPassName() << "\n";
  }
  
  /// Add all LLVM passes into the pass manager.
  inline void addTransformPasses(PassManager &PM) {
    // We perform LCSSA pass before CFGSimplification to avoid doing
    // some code hoisting (HoistThenElseCodeToIf in
    // Transforms/Utils/SimplifyCFG). 
    //
    // Some code hoisting can make us losing precision if
    // simplifications like the following are performed:
    // bb8:
    //   ...
    //   %tmp11 = icmp ne i32 %tmp10, %x
    //   br i1 %tmp11, label %bb13, label %bb15
    // bb13:
    //   %tmp14 = add nsw i32 %i.0, 1
    //   br label %bb8
    // bb15:
    //   %tmp16 = add nsw i32 %i.0, 1
    //   ...
    // 
    // into:
    //
    // bb8: 
    //   ...
    //   %tmp11 = icmp ne i32 %tmp10, %x
    //   %tmp14 = add nsw i32 %i.0, 1
    //   br i1 %tmp11, label %bb8, label %bb15
    // 
    // The analysis rely on being able to filter the value of %i.0 in
    // bb13 using the branch conditional of bb8. If we allow merging
    // then we don't filter the value losing precision.

    if (instCombine){
      // This pass is useful among other things to remove casting
      // operations that may preclude us of refining using branch
      // conditions (e.g., t5-a.c)
      addPass(PM, createInstructionCombiningPass()); // remove redundancies
    }
    
    if (enableOptimizations){
      
      addPass(PM, createLoopSimplifyPass());        // Canonicalize natural loops 
      // addPass(PM, createLoopRotatePass());        
      addPass(PM, createLCSSAPass());               // Loop closed ssa form 
      addPass(PM, createCFGSimplificationPass());   // Clean up

      addPass(PM, createPromoteMemoryToRegisterPass());// Kill useless allocas
      addPass(PM, createDeadArgEliminationPass());   // Dead argument elimination
      addPass(PM, createGlobalDCEPass());            // Remove unused fns and globs
      addPass(PM, createGlobalOptimizerPass());      // optimizes non-address taken internal globals.
      addPass(PM, createCFGSimplificationPass());    // Clean up disgusting code

      addPass(PM, createSCCPPass());                  // Constant prop with SCCP
      addPass(PM, createIPConstantPropagationPass()); // IP Constant Propagation
      addPass(PM, createGVNPass());                   // Remove redundancies (e.g., load)
                                                      // it may introduce PHI nodes!
      addPass(PM, createDeadCodeEliminationPass());   // DCE
      addPass(PM, createAggressiveDCEPass());         // Delete dead instructions
      addPass(PM, createCFGSimplificationPass());     // Clean up after DCE  

      // if (Inline > 0){
      // 	// This pass is useful for obviuos reason but expensive.
      // 	addPass(PM, createFunctionInliningPass(Inline)); // Inline functions
      // 	addPass(PM, createCFGSimplificationPass());      // Clean up after DCE  
      // }

      addPass(PM, createUnifyFunctionExitNodesPass()); // at most one return
      addPass(PM, createCFGSimplificationPass());   // Another clean up
      addPass(PM, createLowerSwitchPass());         // Eliminate switch constructions  
      
    }
    else{
      addPass(PM, createUnifyFunctionExitNodesPass()); // at most one return
      addPass(PM, createLowerSwitchPass());            // Eliminate switch constructions  
    }

    if (instCombine){
      // This pass is useful among other things to remove casting
      // operations that may preclude us of refining using branch
      // conditions (e.g., t5-a.c)
      addPass(PM, createInstructionCombiningPass()); // remove redundancies
    }

    if (Inline > 0){
      // This pass is useful for obviuos reason but expensive.
      addPass(PM, createFunctionInliningPass(Inline)); // Inline functions
      //addPass(PM, createCFGSimplificationPass());      // Clean up after DCE  
    }

    addPass(PM, createvSSAPass());                     // Run vssa pass
  }

  /// To run all the transformations previous to the range analysis.
  struct RangeTransformationPass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    RangeTransformationPass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      PassManager Passes;
      addTransformPasses(Passes);  
      Passes.run(M);

      return true;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
    }    
  };

  char RangeTransformationPass::ID = 0;
  static RegisterPass<RangeTransformationPass> YY("range-transformations",
						  "Transformations needed by the variants of Range Analyses",
						  false,false);


  /// Classical fixed-width range analysis
  class RangeAnalysis: public FixpointSSI {
  private:
    bool IsSigned;
  public:
    RangeAnalysis(Module *M, unsigned WL, unsigned NL, AliasAnalysis *AA,  bool isSigned): 
      FixpointSSI(M,WL,NL,AA,isSigned){
      // Here if we want a signed or unsigned analysis
      IsSigned=isSigned;
    }

    // Methods that allows Fixpoint creates Range objects
    virtual AbstractValue* initAbsValBot(Value *V){
      Range * R = new Range(V,IsSigned);
      R->makeBot();
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsValTop(Value *V){
      Range * R = new Range(V,IsSigned);
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsIntConstant(ConstantInt *C){
      Range * R = new Range(C, C->getBitWidth(),IsSigned);
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsValIntConstant(Value *V, ConstantInt *C){
      Range * RV = new Range(V,IsSigned);
      Range * RC = new Range(C, C->getBitWidth(), IsSigned);
      RV->makeBot();
      RV->join(RC);      
      delete RC;
      assert(RV);
      return RV;
    }
  };


  /// Wrapped Interval Analysis
  class WrappedRangeAnalysis: public FixpointSSI {
  public:
    WrappedRangeAnalysis(Module *M, unsigned WL, unsigned NL, AliasAnalysis *AA): 
      FixpointSSI(M,WL,NL,AA){}

    // Methods that allows Fixpoint creates Range objects
    virtual AbstractValue* initAbsValBot(Value *V){
      WrappedRange * R = new WrappedRange(V);
      R->makeBot();
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsValTop(Value *V){
      WrappedRange * R = new WrappedRange(V);
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsIntConstant(ConstantInt *C){
      WrappedRange * R = new WrappedRange(C, C->getBitWidth());
      assert(R);
      return R;
    }
    virtual AbstractValue* initAbsValIntConstant(Value *V, ConstantInt *C){
      WrappedRange * RV = new WrappedRange(V);
      WrappedRange * RC = new WrappedRange(C, C->getBitWidth());
      assert(RV);
      assert(RC);
      RV->makeBot();
      RV->join(RC);      
      delete RC;
      return RV;
    }
  };


  /// Return true if the analysis will consider F.
  bool IsAnalyzable(const Function *F, CallGraph &CG){
    return (Utilities::IsTrackableFunction(F));

    // The numbers reported in the APLAS paper were obtained by
    // ignoring functions which were not called by "main".
    //if (!Utilities::IsTrackableFunction(F)) return false;
    // if (F->getName() == "main") return true;
    // if (CallGraphNode * CG_F = CG[F]){
    //   if (CG_F->getNumReferences() == 1){
    // 	// The function is either unreachablle, external, or inlined.
    // 	return false;
    //   }
    // }
    //return true;
  }

  /// Common analyses needed by the range analysis.
  inline void RangePassRequirements(AnalysisUsage& AU){
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<DominatorTree>();
    AU.addRequired<CallGraph>();
    AU.setPreservesAll(); // Does not transform code
  }    

  /// To run an intraprocedural range analysis.
  struct RangePass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    RangePass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      dbgs() <<"\n===-------------------------------------------------------------------------===\n" ;  
      dbgs() << "               Range Integer Variable Analysis \n";
      dbgs() <<"===-------------------------------------------------------------------------===\n" ;      
      RangeAnalysis Analysis(&M, widening , narrowing , AA, SIGNED_RANGE_ANALYSIS);
      for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
       	if (IsAnalyzable(F,*CG)){
	  // Function *F = M.getFunction("InitializeFindAttacks"); // for debugging
	  DEBUG(dbgs() << "------------------------------------------------------------------------\n");
	  Analysis.init(F);
	  Analysis.solve(F);
#ifdef  PRINT_RESULTS 	  
	  //Analysis.printResultsGlobals(dbgs());
	  Analysis.printResultsFunction(F,dbgs());
#endif  /*PRINT_RESULTS*/
	}
      }
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  };


  /// To run an intraprocedural wrapped range analysis.
  struct WrappedRangePass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    WrappedRangePass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      dbgs() <<"\n===-------------------------------------------------------------------------===\n";  
      dbgs() << "               Wrapped Range Integer Variable Analysis \n";
      dbgs() <<"===-------------------------------------------------------------------------===\n";      
      WrappedRangeAnalysis Analysis(&M, widening , narrowing , AA);
      for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
	if (IsAnalyzable(F,*CG)){
	  // Function *F = M.getFunction("InitializeFindAttacks"); // for debugging
	  DEBUG(dbgs() << "------------------------------------------------------------------------\n");
	  Analysis.init(F);
	  Analysis.solve(F);
#ifdef  PRINT_RESULTS 	  
	  //Analysis.printResultsGlobals(dbgs());
	  Analysis.printResultsFunction(F,dbgs());
#endif  /*PRINT_RESULTS*/
	}
      }
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  };


  char RangePass::ID = 0;
  static RegisterPass<RangePass> RP("range-analysis",
				    "Fixed-Width Integer Range Analysis",
				    false,false);

  char WrappedRangePass::ID = 0;
  static RegisterPass<WrappedRangePass> WRP("wrapped-range-analysis",
					    "Fixed-Width Wrapped Integer Range Analysis",
					    false,false);


  /// This class runs -range-analysis and -wrapped-range-analysis
  /// passes and gather some numbers regarding precision.
  class generateStatsForPaper : public ModulePass{
    typedef enum {ORD_EQ = 0, ORD_LEQ = 1, ORD_GEQ =2, ORD_NEQ=3} TORD;    
  public:
    // Pass identification, replacement for typeid    
    static char ID; 
    /// Constructor of the class.
    generateStatsForPaper() :  ModulePass(ID), IsAllSigned(SIGNED_RANGE_ANALYSIS),       
			       NumTotal(0), NumOfSame(0), NumOfDifferent(0), 
			       NumUnWrappedIsBetter(0), NumWrappedIsBetter1(0), 
			       NumWrappedIsBetter2(0), 
			       NumOfIncomparable(0), NumOfTrivial(0) { }
    /// Destructor of the class.
    ~generateStatsForPaper(){}
    
    virtual bool runOnModule(Module &M){
     
      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      RangeAnalysis Intervals(&M, widening,narrowing, AA, SIGNED_RANGE_ANALYSIS);
      WrappedRangeAnalysis WrappedIntervals(&M, widening, narrowing,  AA);
      for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
       	if (IsAnalyzable(F,*CG)){
	  // Function *F = M.getFunction("InitializeFindAttacks"); // for debugging
	  dbgs() << "---------------- Function " << F->getName() << "---------------------\n";
	  dbgs() << "----------------   running Range Analysis ... -----------------------\n";
	  Intervals.init(F);
	  Intervals.solve(F);
	  dbgs() << "----------------   running Wrapped Range Analysis ... ---------------\n";
	  WrappedIntervals.init(F);
	  WrappedIntervals.solve(F);
	  // Gather statistics after the analysis of the function.
	  // After than, each analysis will cleanup *all* their
	  // datastructures.
	  compareAnalysesOfFunction(Intervals, WrappedIntervals);
	}
      } // end for
      
      printStats(dbgs());     
      return false;
    }
    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  private:
    bool IsAllSigned;
   
    // Counters
    unsigned NumTotal;
    unsigned NumOfSame;
    unsigned NumOfDifferent;
    unsigned NumUnWrappedIsBetter;
    unsigned NumWrappedIsBetter1; // because unwrapped was top
    unsigned NumWrappedIsBetter2; // neither was top and wrapped is more precise.
    unsigned NumOfIncomparable;
    unsigned NumOfTrivial;

    void compareAnalysesOfFunction(const RangeAnalysis &Intervals,
				   const WrappedRangeAnalysis &WrappedIntervals){

      // We cannot assume a particular order of the entries since LLVM
      // can generate different orders
      AbstractStateTy IntervalMap         = Intervals.getValMap();
      AbstractStateTy WrappedIntervalMap  = WrappedIntervals.getValMap();     
      // This is expensive because is n*m where n,m sizes of the two
      // hash tables. Most of the time, n is equal to m.
      typedef AbstractStateTy::iterator It;
      for (It B=IntervalMap.begin(), E=IntervalMap.end(); B != E; ++B){
	if (!B->second){
	  continue;
	}
	if (Range * I1 = dyn_cast<Range>(B->second)){
	  if (I1 && (!I1->isConstant())){
	    AbstractValue *AbsVal =WrappedIntervalMap[B->first];
	    assert(AbsVal);
	    WrappedRange *I2 = dyn_cast<WrappedRange>(AbsVal);
	    assert(I2);
	    assert(!I2->isConstant());
	    compareTwoIntervals(I1,I2, IsAllSigned); 
	  }
	}
      } // end for
    }

    void compareTwoIntervals(Range *I1, WrappedRange* I2, bool isSigned){
      // WrappedRange normalizes different representations of top but
      // Range does not.
      I1->normalize();
      assert(I1);
      assert(I2);
      
      NumTotal++;
      assert(I1->getWidth() == I2->getWidth());
      assert(I1->getValue() == I2->getValue());

      if (I1->IsTop() && I2->IsTop()){
	NumOfTrivial++;
	return;
      }

      if (I1->isBot() || I2->isBot()){
	NumOfTrivial++;
	return;
      }
	    
      if (I1->IsTop() && !I2->IsTop()){
#ifdef MORE_COMPARISON_DETAILS
	dbgs() << "Wrapped interval won: ";
	I2->print(dbgs());
	dbgs() << " better than ";
	I1->print(dbgs());
	dbgs() << "\n";
#endif /*MORE_COMPARISON_DETAILS*/
	NumWrappedIsBetter1++;
	return;
      }

      if (!I1->IsTop() && I2->IsTop()){
#ifdef MORE_COMPARISON_DETAILS
	dbgs() << "Interval won: ";
	I1->print(dbgs());
	dbgs() << " better than ";
	I2->print(dbgs());
	dbgs() << "\n";
#endif /*MORE_COMPARISON_DETAILS*/
	NumUnWrappedIsBetter++;
	return;
      }
      // Otherwise, we convert the interval into a wrapped interval so
      // that we can compare precision.

      // dbgs() << "BEFORE CONVERSION: " ;
      // dbgs() << "unwrapped:" ;
      // I1->print(dbgs());
      // dbgs() << "\n";

      APInt a = I1->getLB();
      APInt b = I1->getUB();
      WrappedRange * NewI1 = new WrappedRange(a,b,a.getBitWidth());
      if (I1->isBot())
	NewI1->makeBot();
      if (I1->IsTop())
	NewI1->makeTop();

      // dbgs() << "AFTER CONVERSION: " ;
      // dbgs() << "wrapped:" ;
      // NewI1->print(dbgs());
      // dbgs() << "\n";
      
      if (I2->isEqual(NewI1)) {
	NumOfSame++;
	delete NewI1;
	return;
      }


      if ( (I2->WrappedlessOrEqual(NewI1,false))){
	if (NewI1->WrappedlessOrEqual(I2,false))
	  NumOfSame++;
	else{
#ifdef MORE_COMPARISON_DETAILS
	  dbgs() << "Wrapped interval won: ";
	  I2->print(dbgs());
	  dbgs() << " better than ";
	  NewI1->print(dbgs());
	  dbgs() << "\n";
#endif /*MORE_COMPARISON_DETAILS*/
	  NumWrappedIsBetter2++;
	}
      }
      else{
	if (NewI1->WrappedlessOrEqual(I2,false)){
#ifdef MORE_COMPARISON_DETAILS
	  dbgs() << "Interval won: ";
	  NewI1->print(dbgs());
	  dbgs() << " better than ";
	  I2->print(dbgs());
	  dbgs() << "\n";
#endif /*MORE_COMPARISON_DETAILS*/
	  NumUnWrappedIsBetter++;
	}
	else
	  NumOfIncomparable++;
      }      
      delete NewI1;
    } // end function

    void printStats(raw_ostream &Out){
      Out << "=----------------------------------------------------------------------=\n";
      Out << "                         Summary results                                \n";
      Out << "=----------------------------------------------------------------------=\n";
      Out << "# tracked intervals              : "  <<  NumTotal << "\n";
      Out << "# top/bottom intervals           : "  <<  NumOfTrivial << "\n";
      Out << "# non top/bottom  intervals      : "  <<  NumTotal - NumOfTrivial << "\n\n";
      Out << "# intervals same precision       : "  <<  NumOfSame << "\n";
      Out << "# wrapped more precise because unwrappred top : "  <<  NumWrappedIsBetter1   << "   // hopefully > 0. \n";     
      Out << "# wrapped more precise                        : "  <<  NumWrappedIsBetter2   << "   // hopefully > 0. \n";     

      // FIXME: classical intervals cannot be more precise than
      // Wrapped ones. However, it's possible that classical intervals
      // implement a case which is not implemented precisely with
      // Wrapped.
      Out << "# intervals more precise         : "  <<  NumUnWrappedIsBetter << "   // should be 0. \n";
      // Out << "# incomparable intervals         : "  <<  NumOfIncomparable << "\n\n";   
    }
   
  }; // end of class generateStatsForPaper

  char generateStatsForPaper::ID = 0;
  static RegisterPass<generateStatsForPaper> GSFP("compare-range-analyses",
						  "Compare -range-analysis and -wrapped-range-analysis",
						  false,false);

} // end namespace





