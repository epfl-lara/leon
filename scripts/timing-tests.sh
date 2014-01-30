LEON_HOME="/home/kandhada/leon/leon"

#Insertion Sort
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/InsertionSort.scala  --stats-suffix=-nl-stats" > inssort-nl-out.txt

#List operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ListOperations.scala --stats-suffix=-nl-stats" > listoperations-nl-out.txt

#Tree operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/TreeOperations.scala --stats-suffix=-nl-stats --monotones=mult" > treeoperations-nl-out.txt

#Amortized queue
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AmortizedQueue.scala --stats-suffix=-nl-stats" > amortizedqueue-nl-out.txt

#Propositional logic
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/PropositionalLogic.scala --stats-suffix=-nl-stats" > proplogic-nl-out.txt

#Binary trie
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinaryTrie.scala --stats-suffix=-nl-stats" > binarytrie-nl-out.txt

#Leftist heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/LeftistHeap.scala --stats-suffix=-nl-stats --monotones=twopower" > leftistheap-nl-out.txt

#concat variations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ConcatVariations.scala --stats-suffix=-nl-stats --monotones=mult" > concatvars-nl-out.txt

#Binomial Heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinomialHeap.scala --stats-suffix=-nl-stats" > binomialheap-nl-out.txt

#ForElimination
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ForElimination.scala --stats-suffix=-nl-stats" > forelim-nl-out.txt

#AVL tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AVLTree.scala --stats-suffix=-nl-stats" > avl-nl-out.txt

#Redblack  tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/RedBlackTree.scala --stats-suffix=-nl-stats" > rbt-nl-out.txt



