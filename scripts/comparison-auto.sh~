LEON_HOME="/home/kandhada/leon/leon"

#Insertion Sort
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/InsertionSort.scala --inferTemp=true --stats-suffix=-nl-stats" > inssort-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/InsertionSort.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats" > inssort-cegis-out.txt

#List operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/ListOperations.scala --inferTemp=true --stats-suffix=-nl-stats" > listoperations-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/ListOperations.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats" > listoperations-cegis-out.txt

#Tree operations
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/TreeOperations.scala --inferTemp=true --stats-suffix=-nl-stats --timeout=20" > treeoperations-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/TreeOperations.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats --timeout=20" > treeoperations-cegis-out.txt

#Amortized queue
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/AmortizedQueue.scala --inferTemp=true --stats-suffix=-nl-stats" > amortizedqueue-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/AmortizedQueue.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats" > amortizedqueue-cegis-out.txt

#Binary trie
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/BinaryTrie.scala --inferTemp=true --stats-suffix=-nl-stats" > binarytrie-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/BinaryTrie.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats" > binarytrie-cegis-out.txt

#Leftist heap
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/LeftistHeap.scala --inferTemp=true --stats-suffix=-nl-stats" > leftistheap-nl-out.txt
runlim -t 1800 ${LEON_HOME}/leon "--inferInv "${LEON_HOME}"/testcases/ravi-testcases/automatic/LeftistHeap.scala --inferTemp=true --cegis=true --stats-suffix=-cegis-stats" > leftistheap-cegis-out.txt
