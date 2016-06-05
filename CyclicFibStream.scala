[[33mWarning [0m] warning: there were three feature warnings; re-run with -feature for details
[[33mWarning [0m] ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:73:5: Tree val first = s
[[33mWarning [0m] val second = first.tailVal
[[33mWarning [0m] val third = second.tailVal
[[33mWarning [0m] third.tailFun match {
[[33mWarning [0m]   case Susp(fun) =>
[[33mWarning [0m]     toFmatch[() => SCons](fun).fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean]((x0$1 : (BigInt, BigInt) => BigInt, x1$1 : SCons, x2$1 : SCons) => (x0$1, x1$1, x2$1) match {
[[33mWarning [0m]       case (f, xs, ys) if toIs[() => SCons](fun).is[() => SCons](() => zipWithSusp(f, xs, ys)) =>
[[33mWarning [0m]         xs == first && ys == second
[[33mWarning [0m]       case _ =>
[[33mWarning [0m]         false
[[33mWarning [0m]     })
[[33mWarning [0m]   case _ =>
[[33mWarning [0m]     false
[[33mWarning [0m] } is not properly typed (./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:73:5)
               val first = s
               [31m^^^^[0m
[[33mWarning [0m] ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:74:5: Tree val second = first.tailVal
[[33mWarning [0m] val third = second.tailVal
[[33mWarning [0m] third.tailFun match {
[[33mWarning [0m]   case Susp(fun) =>
[[33mWarning [0m]     toFmatch[() => SCons](fun).fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean]((x0$1 : (BigInt, BigInt) => BigInt, x1$1 : SCons, x2$1 : SCons) => (x0$1, x1$1, x2$1) match {
[[33mWarning [0m]       case (f, xs, ys) if toIs[() => SCons](fun).is[() => SCons](() => zipWithSusp(f, xs, ys)) =>
[[33mWarning [0m]         xs == first && ys == second
[[33mWarning [0m]       case _ =>
[[33mWarning [0m]         false
[[33mWarning [0m]     })
[[33mWarning [0m]   case _ =>
[[33mWarning [0m]     false
[[33mWarning [0m] } is not properly typed (./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:74:5)
               val second = first.tailVal
               [31m^^^^[0m
[[33mWarning [0m] ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:75:5: Tree val third = second.tailVal
[[33mWarning [0m] third.tailFun match {
[[33mWarning [0m]   case Susp(fun) =>
[[33mWarning [0m]     toFmatch[() => SCons](fun).fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean]((x0$1 : (BigInt, BigInt) => BigInt, x1$1 : SCons, x2$1 : SCons) => (x0$1, x1$1, x2$1) match {
[[33mWarning [0m]       case (f, xs, ys) if toIs[() => SCons](fun).is[() => SCons](() => zipWithSusp(f, xs, ys)) =>
[[33mWarning [0m]         xs == first && ys == second
[[33mWarning [0m]       case _ =>
[[33mWarning [0m]         false
[[33mWarning [0m]     })
[[33mWarning [0m]   case _ =>
[[33mWarning [0m]     false
[[33mWarning [0m] } is not properly typed (./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:75:5)
               val third = second.tailVal
               [31m^^^^[0m
[[33mWarning [0m] ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:76:19: Tree third.tailFun match {
[[33mWarning [0m]   case Susp(fun) =>
[[33mWarning [0m]     toFmatch[() => SCons](fun).fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean]((x0$1 : (BigInt, BigInt) => BigInt, x1$1 : SCons, x2$1 : SCons) => (x0$1, x1$1, x2$1) match {
[[33mWarning [0m]       case (f, xs, ys) if toIs[() => SCons](fun).is[() => SCons](() => zipWithSusp(f, xs, ys)) =>
[[33mWarning [0m]         xs == first && ys == second
[[33mWarning [0m]       case _ =>
[[33mWarning [0m]         false
[[33mWarning [0m]     })
[[33mWarning [0m]   case _ =>
[[33mWarning [0m]     false
[[33mWarning [0m] } is not properly typed (./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:76:19)
               third.tailFun match {
                             [31m^[0m
[[33mWarning [0m] ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:78:13: Tree toFmatch[() => SCons](fun).fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean]((x0$1 : (BigInt, BigInt) => BigInt, x1$1 : SCons, x2$1 : SCons) => (x0$1, x1$1, x2$1) match {
[[33mWarning [0m]   case (f, xs, ys) if toIs[() => SCons](fun).is[() => SCons](() => zipWithSusp(f, xs, ys)) =>
[[33mWarning [0m]     xs == first && ys == second
[[33mWarning [0m]   case _ =>
[[33mWarning [0m]     false
[[33mWarning [0m] }) is not properly typed (./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala:78:13)
                   fun fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean] {
                       [31m^^^^^^[0m
[[34m  Info  [0m] Output written on leon.out
Escaping types: BigIntxBigInttBigInt,tSCons

[[34m  Info  [0m] Output written on leon.out
[[34m  Info  [0m] Output written on leon.out
[[34m  Info  [0m] Output written on leon.out
[[34m  Info  [0m] Output written on leon.out
instfuncs: fval-mem,utSCons,uBigIntxBigInttBigInt,eval@tSCons@,nthElemAfterThird,nthFib,eval@BigIntxBigInttBigInt@,zipWithFun,genNext,zipWithSusp,next instFuncTypes: 
[[34m  Info  [0m] Output written on leon.out
[[34m  Info  [0m] Output written on leon.out
[[34m  Info  [0m] Output written on leon.out
instfuncs:  instFuncTypes: 
[[34m  Info  [0m] - Nothing to solve for utSCons-time
[[34m  Info  [0m] - Nothing to solve for uBigIntxBigInttBigInt-time
[[34m  Info  [0m] - considering function zipWithFun-time...
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] zipWithFun-time-->res76._2 <= 0
[[34m  Info  [0m] checked VC inst... in 0.042s
[[34m  Info  [0m] Function: zipWithFun-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.036s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] zipWithFun-time-->res76._2 <= 0
[[34m  Info  [0m] checked VC inst... in 0.013s
[[34m  Info  [0m] Function: zipWithFun-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.018s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] zipWithFun-time-->res76._2 + -15 <= 0
[[34m  Info  [0m] checked VC inst... in 0.01s
[[34m  Info  [0m] Function: zipWithFun-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.01s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] zipWithFun-time-->res76._2 <= 0
[[34m  Info  [0m] checked VC inst... in 0.011s
[[34m  Info  [0m] Function: zipWithFun-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.008s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] zipWithFun-time-->res76._2 + -15 <= 0
[[34m  Info  [0m] checked VC inst... in 0.008s
[[34m  Info  [0m] Function: zipWithFun-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.01s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] - Cannot do more unrollings, reached unroll bound
[[34m  Info  [0m] - Exhausted all templates, cannot infer invariants
[[34m  Info  [0m] - considering function zipWithSusp-time...
[[34m  Info  [0m] - considering function fval-mem-time...
[[34m  Info  [0m] - considering function next-time...
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 <= 0
[[34m  Info  [0m] checked VC inst... in 0.029s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -7 <= 0
[[34m  Info  [0m] checked VC inst... in 0.017s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.011s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 <= 0
[[34m  Info  [0m] checked VC inst... in 0.053s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -7 <= 0
[[34m  Info  [0m] checked VC inst... in 0.089s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 <= 0
[[34m  Info  [0m] checked VC inst... in 1.43s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -7 <= 0
[[34m  Info  [0m] checked VC inst... in 0.279s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] - More unrollings for invariant inference
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 <= 0
[[34m  Info  [0m] checked VC inst... in 7.422s
[[34m  Info  [0m] Function: next-time--Found candidate invariant is not a real invariant! 
[[34m  Info  [0m] # of atomic predicates: 6 + 1
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.008s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -7 <= 0
[[34m  Info  [0m] checked VC inst... in 15.045s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 7
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.012s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -15 <= 0
[[34m  Info  [0m] checked VC inst... in 15.035s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 8
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -31 <= 0
[[34m  Info  [0m] checked VC inst... in 15.036s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 9
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -63 <= 0
[[34m  Info  [0m] checked VC inst... in 15.033s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 10
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -127 <= 0
[[34m  Info  [0m] checked VC inst... in 15.035s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 11
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -255 <= 0
[[34m  Info  [0m] checked VC inst... in 15.041s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 12
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.01s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -511 <= 0
[[34m  Info  [0m] checked VC inst... in 15.045s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 13
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.011s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -1023 <= 0
[[34m  Info  [0m] checked VC inst... in 15.037s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 14
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.018s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -2047 <= 0
[[34m  Info  [0m] checked VC inst... in 15.034s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 15
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.008s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -4095 <= 0
[[34m  Info  [0m] checked VC inst... in 15.04s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 16
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -8191 <= 0
[[34m  Info  [0m] checked VC inst... in 15.034s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 17
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.011s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -16383 <= 0
[[34m  Info  [0m] checked VC inst... in 15.034s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 18
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -32767 <= 0
[[34m  Info  [0m] checked VC inst... in 15.041s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 19
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.009s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -65535 <= 0
[[34m  Info  [0m] checked VC inst... in 15.032s
[[34m  Info  [0m] VC solving failed!...retrying with a bigger model...
[[34m  Info  [0m] # of atomic predicates: 2 + 20
[[34m  Info  [0m] solving...
[[34m  Info  [0m] solved... in 0.007s
[[34m  Info  [0m] Candidate invariants
[[34m  Info  [0m] next-time-->x$129._2 + -131071 <= 0
