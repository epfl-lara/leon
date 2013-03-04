LEON_HOME="/home/kandhada/leon/leon"

#Insertion Sort
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/InsertionSort.scala  --stats-suffix=-nl-stats --fullunroll" > inssort-nl-out.txt

#List operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ListOperations.scala --stats-suffix=-nl-stats --fullunroll" > listoperations-nl-out.txt

#Tree operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/TreeOperations.scala --stats-suffix=-nl-stats --monotones=mult --fullunroll" > treeoperations-nl-out.txt

#Amortized queue
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AmortizedQueue.scala --stats-suffix=-nl-stats --fullunroll" > amortizedqueue-nl-out.txt

#Propositional logic
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/PropositionalLogic.scala --stats-suffix=-nl-stats --fullunroll" > proplogic-nl-out.txt

#Binary trie
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinaryTrie.scala --stats-suffix=-nl-stats --fullunroll" > binarytrie-nl-out.txt

#Leftist heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/LeftistHeap.scala --stats-suffix=-nl-stats --monotones=twopower --fullunroll" > leftistheap-nl-out.txt

#concat variations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/ConcatVariations.scala --stats-suffix=-nl-stats --monotones=mult --fullunroll" > concatvars-nl-out.txt

#Redblack  tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/RedBlackTree.scala --stats-suffix=-nl-stats --fullunroll" > rbt-nl-out.txt

#AVL tree
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/AVLTree.scala --stats-suffix=-nl-stats --fullunroll" > avl-nl-out.txt

#Binomial Heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/timing/BinomialHeap.scala --stats-suffix=-nl-stats --fullunroll" > binomialheap-nl-out.txt
