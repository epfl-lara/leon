LEON_HOME="/home/kandhada/leon/leon"

#Insertion Sort
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/InsertionSort.scala  --stats-suffix=-nl-stats --cegis" > inssort-nl-out.txt

#List operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ListOperations.scala --stats-suffix=-nl-stats --cegis" > listoperations-nl-out.txt

#Tree operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/TreeOperations.scala --stats-suffix=-nl-stats --cegis" > treeoperations-nl-out.txt

#Amortized queue
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AmortizedQueue.scala --stats-suffix=-nl-stats --cegis" > amortizedqueue-nl-out.txt

#Propositional logic
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/PropositionalLogic.scala --stats-suffix=-nl-stats --cegis" > proplogic-nl-out.txt

#Binary trie
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinaryTrie.scala --stats-suffix=-nl-stats --cegis" > binarytrie-nl-out.txt

#Speed Benchmarks
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/SpeedBenchmarks.scala --stats-suffix=-nl-stats --cegis" > speed-nl-out.txt

#Leftist heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/LeftistHeap.scala --stats-suffix=-nl-stats --cegis" > leftistheap-nl-out.txt

#concat variations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ConcatVariations.scala --stats-suffix=-nl-stats --cegis" > concatvars-nl-out.txt

#Binomial Heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinomialHeap.scala --stats-suffix=-nl-stats --cegis" > binomialheap-nl-out.txt

#ForElimination
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ForElimination.scala --stats-suffix=-nl-stats --cegis" > forelim-nl-out.txt

#AVL tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AVLTree.scala --stats-suffix=-nl-stats --cegis" > avl-nl-out.txt

#Redblack  tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/RedBlackTree.scala --stats-suffix=-nl-stats --cegis" > rbt-nl-out.txt

#Folds
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/Folds.scala --stats-suffix=-nl-stats --cegis" > folds-nl-out.txt

