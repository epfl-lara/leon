./leon --mem --benchmark --timeout=1800 ./testcases/lazy-datastructures/withOrb/SortingnConcat.scala | tee SortingnConcat.out # runs in a few seconds
./leon --mem --benchmark --unrollfactor=2  --timeout=1800 ./testcases/lazy-datastructures/withOrb/RealTimeQueue.scala | tee  RealTimeQueue.out # take ~1min
./leon --mem --benchmark --unrollfactor=4  --timeout=1800 ./testcases/lazy-datastructures/withOrb/CyclicFibStream.scala  | tee CyclicFibStream.out # a few secs
./leon --mem --benchmark --unrollfactor=2  --timeout=1800 ./testcases/lazy-datastructures/withOrb/PreciseBottomUpMegeSort.scala | tee PreciseBottomUpMegeSort.out
./leon --mem --benchmark --unrollfactor=5  --timeout=1800 ./testcases/lazy-datastructures/withOrb/LazyNumericalRep.scala  | tee LazyNumericalRep.out # in a few secs
./leon --mem --benchmark --unrollfactor=4   --timeout=1800 ./testcases/lazy-datastructures/withOrb/Deque.scala | tee Deque.out # takes ~ 2min
./leon --mem --benchmark --unrollfactor=4  --timeout=1800 ./testcases/lazy-datastructures/withOrb/CyclicHammingStream.scala  | tee CyclicHammingStream.out # takes about 2 min
./leon --mem --benchmark  --timeout=1800 ./testcases/lazy-datastructures/withOrb/RunningExample.scala | tee RunningExample.out # a few secs
./leon --mem --benchmark  --timeout=1800 ./testcases/lazy-datastructures/withOrb/Knapsack.scala  | tee Knapsack.out # a few seconds
./leon --mem --benchmark  --timeout=1800 ./testcases/lazy-datastructures/withOrb/WeightedScheduling.scala | tee Sched.out # a few seconds
./leon --mem --benchmark --unrollfactor=2  --timeout=1800 ./testcases/lazy-datastructures/withOrb/LongestCommonSubsequence.scala  | tee LongestCommonSubsequence.out # a few seconds
./leon --mem --benchmark --unrollfactor=2  --timeout=1800 ./testcases/lazy-datastructures/withOrb/LevenshteinDistance.scala  | tee LevenshteinDistance.out # a few seconds
./leon --mem --benchmark --unrollfactor=4  --timeout=1800 ./testcases/lazy-datastructures/withOrb/PackratParsing.scala  | tee PackratParsing.out # ~ 1min
./leon --mem --benchmark  --timeout=1800 ./testcases/lazy-datastructures/withOrb/Haskell-Library/StreamLibrary.scala ./testcases/lazy-datastructures/withOrb/Haskell-Library/StreamClient.scala | tee StreamLibrary.out
./leon --mem --benchmark --unrollfactor=5  --timeout=1800 ./testcases/lazy-datastructures/conc/ConcTrees.scala ./testcases/lazy-datastructures/conc/Conqueue.scala | tee Conqueue.out
./leon --mem --benchmark --unrollfactor=3  --timeout=1800 ./testcases/lazy-datastructures/withOrb/HammingMemoized.scala | tee HammingMemoized.out   # may take up to 1000s need to optimize
#./leon --mem --benchmark --unrollfactor=3 --vcTimeout=35 ./testcases/lazy-datastructures/withOrb/BottomUpMegeSort.scala | tee BottomUpMegeSort.out	# works in ~ 5 min, but a time bound of a function is manually provided
