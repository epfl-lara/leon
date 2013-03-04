LEON_HOME="/home/kandhada/leon/leon"

${LEON_HOME}/leon --genHorn --outfilename="list-append.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/ListAppend.scala
${LEON_HOME}/leon --genHorn --outfilename="list-reverse.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/ListRev.scala
${LEON_HOME}/leon --genHorn --outfilename="list-reverse2.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/ListRev2.scala
${LEON_HOME}/leon --genHorn --outfilename="tree-size.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/Size.scala
${LEON_HOME}/leon --genHorn --outfilename="size-height.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/SizeAndHeight.scala
${LEON_HOME}/leon --genHorn --outfilename="insertion-sort.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/InsertionSort.scala
${LEON_HOME}/leon --genHorn --outfilename="propositional-logic.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/PropositionalLogic.scala
${LEON_HOME}/leon --genHorn --outfilename="quick-sort.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/QuickSort.scala
${LEON_HOME}/leon --genHorn --outfilename="leftist-heap.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/LeftistHeap.scala
${LEON_HOME}/leon --genHorn --outfilename="heap-sort.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/HeapSort.scala
${LEON_HOME}/leon --genHorn --outfilename="binary-trie.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/BinaryTrie.scala
${LEON_HOME}/leon --genHorn --outfilename="AVL-tree.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/AVLTree.scala
${LEON_HOME}/leon --genHorn --outfilename="red-black-tree.smt2" ${LEON_HOME}/testcases/ravi-testcases/Basic/RedBlackTree.scala

#Tests (comment this out later)

echo "checking list-append..."
z3 -smt2 list-append.smt2
echo "checking list-reverse..."
z3 -smt2 list-reverse.smt2
echo "checking list-reverse2..."
z3 -smt2 list-reverse2.smt2
echo "checking tree-size..."
z3 -smt2 tree-size.smt2
echo "checking size-height..."
z3 -smt2 size-height.smt2
echo "checking insertion-sort..."
z3 -smt2 insertion-sort.smt2
echo "checking propositional-logic..."
z3 -smt2 propositional-logic.smt2
echo "checking quick-sort..."
z3 -smt2 quick-sort.smt2
echo "checking lefist-heap..."
z3 -smt2 leftist-heap.smt2
echo "checking heap-sort..."
z3 -smt2 heap-sort.smt2
echo "checking binary-trie..."
z3 -smt2 binary-trie.smt2
echo "checking AVL-tree..."
z3 -smt2 AVL-tree.smt2
echo "checking red-black-tree..."
z3 -smt2 red-black-tree.smt2
