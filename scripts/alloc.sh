LEON_HOME="../../../"
# lazy data structures
${LEON_HOME}/leon --mem --benchmark --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/LazySelectionSort.scala | tee LazySelectionSort.out # runs in a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/PrimeStream.scala | tee PrimeStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/CyclicFibStream.scala  | tee CyclicFibStream.out # a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/CyclicHammingStream.scala  | tee CyclicHammingStream.out # takes about 2 min#${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/StreamLibrary/StreamLibrary.scala ${LEON_HOME}/testcases/benchmarks/alloc/StreamLibrary/StreamClient.scala | tee StreamLibrary.out#${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/RealTimeQueue.scala | tee  RealTimeQueue.out # take ~1min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/BottomUpMergeSort.scala | tee BottomUpMergeSort.out
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/StreamLibrary/StreamLibrary.scala ${LEON_HOME}/testcases/benchmarks/alloc/StreamLibrary/StreamClient.scala | tee StreamLibrary.out
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/RealTimeQueue.scala | tee  RealTimeQueue.out # take ~1min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4   --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/Deque.scala | tee Deque.out # takes ~ 2min
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/LazyNumericalRep.scala  | tee LazyNumericalRep.out # in a few secs
${LEON_HOME}/leon --mem --benchmark --unrollfactor=5  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/Conqueue/ConcTrees.scala ${LEON_HOME}/testcases/benchmarks/alloc/Conqueue/Conqueue.scala | tee Conqueue.out
# Dynamic programming
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/LongestCommonSubsequence.scala  | tee LongestCommonSubsequence.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=2  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/LevenshteinDistance.scala  | tee LevenshteinDistance.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=3  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/HammingMemoized.scala | tee HammingMemoized.out  
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/WeightedScheduling.scala | tee Sched.out # a few seconds
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/Knapsack.scala  | tee Knapsack.out # a few seconds
${LEON_HOME}/leon --mem --benchmark --unrollfactor=4  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/PackratParsing.scala  | tee PackratParsing.out # ~ 1min
${LEON_HOME}/leon --mem --benchmark  --timeout=1800 ${LEON_HOME}/testcases/benchmarks/alloc/Viterbi.scala  | tee Viterbi.out # a few seconds
