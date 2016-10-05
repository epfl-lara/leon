LEON_HOME="../../"
# lazy data structures
${LEON_HOME}/leon --mem --benchmark --timeout=1800 ${LEON_HOME}testcases/benchmarks/LazySelectionSort.scala | tee LazySelectionSort.out # runs in a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}testcases/benchmarks/PrimeStream.scala | tee PrimeStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}testcases/benchmarks/CyclicFibStream.scala  | tee CyclicFibStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}testcases/benchmarks/CyclicHammingStream.scala  | tee CyclicHammingStream.out # takes about 2 min
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}testcases/benchmarks/StreamLibrary/StreamLibrary.scala ${LEON_HOME}testcases/benchmarks/StreamLibrary/StreamClient.scala | tee StreamLibrary.out
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}testcases/benchmarks/RealTimeQueue.scala | tee  RealTimeQueue.out # take ~1min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}testcases/benchmarks/BottomUpMergeSort.scala | tee BottomUpMergeSort.out
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4   --timeout=1800 ${LEON_HOME}testcases/benchmarks/Deque.scala | tee Deque.out # takes ~ 2min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}testcases/benchmarks/LazyNumericalRep.scala  | tee LazyNumericalRep.out # in a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}testcases/benchmarks/Conqueue/ConcTrees.scala ${LEON_HOME}testcases/benchmarks/Conqueue/Conqueue.scala | tee Conqueue.out
# Dynamic programming
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}testcases/benchmarks/LongestCommonSubsequence.scala  | tee LongestCommonSubsequence.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}testcases/benchmarks/LevenshteinDistance.scala  | tee LevenshteinDistance.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}testcases/benchmarks/HammingMemoized.scala | tee HammingMemoized.out  
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}testcases/benchmarks/WeightedScheduling.scala | tee Sched.out # a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}testcases/benchmarks/Knapsack.scala  | tee Knapsack.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}testcases/benchmarks/PackratParsing.scala  | tee PackratParsing.out # ~ 1min
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}testcases/benchmarks/Viterbi.scala  | tee Viterbi.out # a few seconds