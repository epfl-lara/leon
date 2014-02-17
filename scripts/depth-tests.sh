LEON_HOME="/home/kandhada/leon/leon"

#Tree maps
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/Folds.scala --stats-suffix=-nl-stats" > folds-nl-out.txt

#Propositional logic
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/PropLogicDepth.scala --stats-suffix=-nl-stats" > proplogic-nl-out.txt

#Quick sort
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/QSortDepth.scala --stats-suffix=-nl-stats" > qsort-nl-out.txt

#Merge sort
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/MergeSort.scala --stats-suffix=-nl-stats" > mergesort-nl-out.txt

#Insertion Sort
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/InsertionSort.scala  --stats-suffix=-nl-stats" > inssort-nl-out.txt

#List operations
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/ListOperations.scala --stats-suffix=-nl-stats" > listoperations-nl-out.txt

#Tree operations
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/TreeOperations.scala --stats-suffix=-nl-stats" > treeoperations-nl-out.txt

#Amortized queue
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/AmortizedQueue.scala --stats-suffix=-nl-stats" > amortizedqueue-nl-out.txt

#Binary trie
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/BinaryTrie.scala --stats-suffix=-nl-stats" > binarytrie-nl-out.txt

#Leftist heap
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/LeftistHeap.scala --stats-suffix=-nl-stats" > leftistheap-nl-out.txt

#concat variations
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/ConcatVariations.scala --stats-suffix=-nl-stats" > concatvars-nl-out.txt

#Binomial Heap
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/BinomialHeap.scala --stats-suffix=-nl-stats" > binomialheap-nl-out.txt

#ForElimination
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/ForElimination.scala --stats-suffix=-nl-stats" > forelim-nl-out.txt

#Speed benchmarks
runlim -t 200 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/SpeedBenchmarks.scala --stats-suffix=-nl-stats" > speed-nl-out.txt

#AVL tree
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/AVLTree.scala --stats-suffix=-nl-stats" > avl-nl-out.txt

#Redblack  tree
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/depth/RedBlackTree.scala --stats-suffix=-nl-stats" > rbt-nl-out.txt
