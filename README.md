# Wrapped Interval Analysis 

**NEWS (12/10/2017)**: This repo is obsolete and it is not currently maintained. However, the Wrapped Interval Domain is implemented in Crab (https://github.com/seahorn/crab) and using Crab-LLVM (https://github.com/seahorn/crab-llvm) you can infer wrapped intervals from LLVM bitcode. 


This project provides the implementation of a new interval analysis,
called wrapped interval analysis. It is implemented in C++ using the
LLVM framework, and currently, it has only support for C programs
which are translated to LLVM IR (Intermediate Representation) via
Clang.

# Installation 

## Checkout and installation of LLVM and Clang 

1. Get the required tools
   - See http://llvm.org/docs/GettingStarted.html#requirements

2. Checkout LLVM:
   - ```LLVM_ROOT=any_directory_you_like```
   - ```cd $LLVM_ROOT```
   - ```svn co -r 139364 http://llvm.org/svn/llvm-project/llvm/trunk llvm``` 

3. Checkout Clang (C/C++ frontend):
   - ```cd $LLVM_ROOT/llvm/tools```
   - ```svn co -r 139290 http://llvm.org/svn/llvm-project/cfe/trunk clang```

4. Build LLVM and Clang:

   - ```cd $LLVM_ROOT/llvm```
   - ```mkdir build``` 
   - ```cd build```
   - ```../configure -enable-optimized=no CC="gcc -m32" CXX="g++ -m32"```
   - ```make``` 
   This builds both LLVM and Clang for debug mode.

## Checkout and installation of the Wrapped Interval Analysis 

- ```git clone https://github.com/sav-project/wrapped-intervals.git```
- ```cd wrapped-intervals```
- ```./configure --with-llvmsrc=$LLVM_ROOT/llvm --with-llvmobj=$LLVM_ROOT/llvm/build```
- ```./make```
- ```cd ./docs && make```  (optional)
- Change ```$CLANG_PATH``` and ```$OPT_PATH``` in the ```tools/run.sh``` script


# Usage 

```
tools/run.sh prog[.c|.bc]  Pass [options] 

Pass is the pass that we want to run: 
  -wrapped-range-analysis        fixed-width wrapped interval analysis
  -range-analysis                fixed-width classical interval analysis
    options:
      -widening n                n is the widening threshold (0: no widening)
      -narrowing n               n is the number of narrowing iterations (0: no narrowing)
      -alias                     by default, -no-aa which always return maybe. If enabled 
                                 then -basic-aa and -globalsmodref-aa are run to be more precise
                                 with global variables.
      -enable-optimizations      enable LLVM optimizations
      -inline n                  inline function calls whenever possible if the size of 
                                 the function is less than n. (0: no inlining). 
                                 A reasonable threshold n is, e.g., 255.
      -instcombine               remove redundant instructions.
                                 It can improve precision by removing problematic casting 
                                 instructions among many other things.
      -insert-ioc-traps          Compile .c program with -fcatch-undefined-ansic-behavior 
                                 which generates IOC trap blocks.  
                                 Note: clang version must support -fcatch-undefined-ansic-behavior    
                       
  general options:
    -help                          print this message
    -stats                         print stats
    -time                          print LLVM time passes
    -dot-cfg                       print .dot file of the LLVM IR
    -debug                         print debugging messages
```

# Background 

The goal of interval analysis is to determine an approximation of the
sets of possible values that may be stored in integer-valued variables
at various points in a computation. To keep this tractable, interval
analysis approximates such a set by keeping only its smallest and
largest possible value. Interval analysis is not new and in fact, it
has had a long history being a frequent example of abstract
interpretation since the field was defined by P. and R. Cousot in
1977.

One motivation for this project is that most programming languages,
included C, provide one or more fixed-width integer types and
arithmetic operations on these types do not have the usual integer
semantics but instead, they obey laws of modular arithmetic. However,
interval analysis implementations often assume that integers have
unlimited precision which is unsound in presence of overflows. One
easy way of fixing this is to assume top whenever overflow is possible
but this can easily lead to an important loss of precision.

## Example

```
char modulo(char x, char y, int p){
  y=-10;
  if(p) x=0;
  else  x=100;
  while (x >= y){      // line 1
    x = x-y;           // line 2 
  }                    // line 3 
  return x;            // line 4
}
```

Traditional interval analysis would ignore the fixed-width nature of
variables, in this case leading to the incorrect conclusion that ```line
4``` is unreachable. A (traditional) width aware interval analysis can do
better. During analysis it finds that, just before ```line 2```,
```x=[0,120]```. Performing ```line 2```'s abstract subtraction operation, it
observes the wrap-around, and finds that ```x = [-128,127]``` at ```line 3```, and
that ```x = [-128,-11]``` at ```line 4``` (with the help of the conditional branch
```x < y```), and as the result of the function call. Although this result
is correct it is a bit disappointing as we will discuss below.

The other motivation has been the fact that LLVM IR carefully
specifies the bit-width of all integer values, but in most cases does
not specify whether values are signed or unsigned. This is because,
for most operations, two's complement arithmetic (treating the inputs
as signed numbers) produces the same bit-vectors as unsigned
arithmetic. Only for operations that must behave differently for
signed and unsigned numbers, such as comparison operations, does LLVM
code indicate whether operands are signed or unsigned. In general it
is not possible to determine which LLVM variables are signed and which
are unsigned. One simple solution is to assume that all integers are
either signed or unsigned but very importantly, no matter which
decision is taken it can always lead to a loss of precision.

- If we treat all numbers are signed:

Assume ```x=0110``` and ```y=[0001,0011]``` in 4 bits. Note that we represent
intervals as bit-patterns. The operation ```x+y``` returns
```[0111,1001]``` ([7,9]) if variables are treated as unsigned. However, if
they are treated as signed then the addition will be deemed to
wraparound, given ```[1000,0111]``` which corresponds to the largest
interval [-8,7].

- If we treat all numbers are unsigned:

Assume now ```x=1110``` and ```y=[0001,0011]``` also in 4 bits. The operation ```x+y```
returns ```[1111,0001]``` ([-1,1]) if variables are treated as
signed. However, if they are treated as unsigned then the addition
will also wraparound.

#Our Contribution

We have implemented another interval analysis based on a new abstract
domain called wrapped intervals which fits naturally with the LLVM
IR. In wrapped intervals each bound is treated as merely a
bit-pattern, considering only its signedness when necessary for the
operation involved (e.g., comparisons and division). This
interpretation based on bit-patterns allows wrapped intervals choosing
always the best results between the unsigned and signed
version. Moreover, wrapped intervals are allowed to wraparound without
going to top directly as fixed-width interval domain would do. The two
cases where either the interval would overflow or not are kept track
by having a special type of disjunctive interval information.

Based on our experimental evaluation with SPEC CPU 2000 programs,
wrapped intervals are more precise than classical interval analysis
but still quite efficient (just a constant factor overhead with
respect to the classical interval domain).

Coming back to the modulo example with wrapped intervals.

Inspection of the code tells us that the result of such a call must
always be smaller than -118, since at each iteration, x increases by
10, and if ```x = [-118,-11]``` at ```line 4```, then on the previous iteration ```x
= [-128,-11]```, so the loop would have terminated. Thus we would have
hoped for the analysis result ```x = [-128,-119]```. The traditional bounds
analysis misses this result because it considers wrap around to be
a leap to the opposite end of the number line, rather than the
incremental step that it is. Using our proposed domain gives the
precision we hoped for. Finding again that ```x = [0,120]``` at ```line 2```, we
derive the bounds ```x = [10,127]``` \/ ```x=[-128,-126]``` (x is in ```[10,127]``` or
in ```[-128,-126]```) at ```line 3```. On the next iteration we have ```x = [0,127]```
\/ ```x = [-128,-126]``` at ```line 1```, ```x = [0,127]``` at ```line 2```, and ```x = [10,127]```
\/ ```x = [-128,-119]``` at ```line 3```. This yields ```x = [-128,-119]``` at ```line 4```,
and one more iteration proves this to be a fixed point.

#References

The wrapped interval analysis is based on these two papers:

1. "Signedness-Agnostic Program Analysis: Precise Integer Bounds for
   Low-Level Code"
   [(PDF)](http://www.cliplab.org/~jorge/docs/wrapped-intervals-aplas12.pdf).
   APLAS 2012.

2. "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance
   Is Bliss"
   [(PDF)](https://ti.arc.nasa.gov/publications/20091/download/). TOPLAS, 2015.

A great paper to understand the issues of integer overflow and defined
vs undefined wraparound:

- "Understanding Integer Overflow in C/C++" by Will Dietz, Peng Li, John
Regehr, and Vikram Adve. Published in ICSE 2012. 

