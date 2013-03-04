LEON_HOME="/home/kandhada/leon/leon"

#Insertion Sort
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/InsertionSort.scala --inferTemp --stats-suffix=-nl-stats" > inssort-nl-out.txt

#List operations
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/ListOperations.scala --inferTemp --stats-suffix=-nl-stats" > listoperations-nl-out.txt

#Tree operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/TreeOperations.scala --inferTemp --stats-suffix=-nl-stats" > treeoperations-nl-out.txt

#Amortized queue
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/AmortizedQueue.scala --inferTemp --stats-suffix=-nl-stats" > amortizedqueue-nl-out.txt

#Binary trie
#runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/BinaryTrie.scala --inferTemp --stats-suffix=-nl-stats" > binarytrie-nl-out.txt

#Leftist heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/LeftistHeap.scala --inferTemp --stats-suffix=-nl-stats" > leftistheap-nl-out.txt
