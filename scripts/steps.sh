LEON_HOME="../../"
# lazy data structures
${LEON_HOME}/leon --mem --benchmark --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/LazySelectionSort.scala | tee LazySelectionSort.out # runs in a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/PrimeStream.scala | tee PrimeStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/steps/CyclicFibStream.scala  | tee CyclicFibStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/CyclicHammingStream.scala  | tee CyclicHammingStream.out # takes about 2 min
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/StreamLibrary/StreamLibrary.scala ${LEON_HOME}/testcases/benchmarks/steps/StreamLibrary/StreamClient.scala | tee StreamLibrary.out
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/RealTimeQueue.scala | tee  RealTimeQueue.out # take ~1min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/BottomUpMergeSort.scala | tee BottomUpMergeSort.out
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4   --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/Deque.scala | tee Deque.out # takes ~ 2min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/LazyNumericalRep.scala  | tee LazyNumericalRep.out # in a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/Conqueue/ConcTrees.scala ${LEON_HOME}/testcases/benchmarks/steps/Conqueue/Conqueue.scala | tee Conqueue.out
# Dynamic programming
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/LongestCommonSubsequence.scala  | tee LongestCommonSubsequence.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/LevenshteinDistance.scala  | tee LevenshteinDistance.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/HammingMemoized.scala | tee HammingMemoized.out  
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/WeightedScheduling.scala | tee Sched.out # a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/Knapsack.scala  | tee Knapsack.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/PackratParsing.scala  | tee PackratParsing.out # ~ 1min
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/steps/Viterbi.scala  | tee Viterbi.out # a few seconds
