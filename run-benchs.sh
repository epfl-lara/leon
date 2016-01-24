./leon --lazy ./testcases/lazy-datastructures/RealTimeQueue.scala | tee  RTQ.out
./leon --lazy ./testcases/lazy-datastructures/BottomUpMegeSort.scala | tee MsortBU.out
./leon --lazy ./testcases/lazy-datastructures/SortingnConcat.scala | tee Sort.out
./leon --lazy ./testcases/lazy-datastructures/Esop15Benchmarks.scala | tee  Esop.out
./leon --lazy ./testcases/lazy-datastructures/RealTimeDeque.scala --unfoldFactor=2 | tee RDQ.out
./leon --lazy ./testcases/lazy-datastructures/LazyNumericalRep.scala --unfoldFactor=3 | tee Num.out
./leon --lazy ./testcases/lazy-datastructures/conc/Conqueue.scala --unfoldFactor=3 | tee Conqueue.out
./leon --lazy ./testcases/lazy-datastructures/memoization/Knapsack.scala | tee Knapsack.out
./leon --lazy ./testcases/lazy-datastructures/memoization/PackratParsing.scala | tee Packrat.out
./leon --lazy ./testcases/lazy-datastructures/memoization/WeightedScheduling.scala | tee Sched.out
