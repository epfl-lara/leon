./leon --genHorn --outfilename="tree-size.smt" ./testcases/ravi-testcases/Basic/Size.scala
./leon --genHorn --outfilename="list-reverse.smt" ./testcases/ravi-testcases/Basic/ListRev.scala
./leon --genHorn --outfilename="list-reverse2.smt" ./testcases/ravi-testcases/Basic/ListRev2.scala
./leon --genHorn --outfilename="list-append.smt" ./testcases/ravi-testcases/Basic/ListAppend.scala
./leon --genHorn --outfilename="size-height.smt" ./testcases/ravi-testcases/Basic/SizeAndHeight.scala
./leon --genHorn --outfilename="insertion-sort.smt" ./testcases/ravi-testcases/Basic/InsertionSort.scala
./leon --genHorn --outfilename="propositional-logic.smt" ./testcases/ravi-testcases/Basic/PropositionalLogic.scala
./leon --genHorn --outfilename="quick-sort.smt" ./testcases/ravi-testcases/Basic/QuickSort.scala
./leon --genHorn --outfilename="leftist-heap.smt" ./testcases/ravi-testcases/Basic/LeftistHeap.scala
./leon --genHorn --outfilename="heap-sort.smt" ./testcases/ravi-testcases/Basic/HeapSort.scala
./leon --genHorn --outfilename="binary-trie.smt" ./testcases/ravi-testcases/Basic/BinaryTrie.scala
./leon --genHorn --outfilename="AVL-tree.smt" ./testcases/ravi-testcases/Basic/AVLTree.scala
./leon --genHorn --outfilename="red-black-tree.smt" ./testcases/ravi-testcases/Basic/RedBlackTree.scala

#Tests (comment this out later)

#echo "checking tree-size..."
#z3 -smt2 tree-size.smt
#echo "checking list-reverse..."
#z3 -smt2 list-reverse.smt
#echo "checking list-reverse2..."
#z3 -smt2 list-reverse2.smt
#echo "checking list-append..."
#z3 -smt2 list-append.smt
#echo "checking size-height..."
#z3 -smt2 size-height.smt
#echo "checking insertion-sort..."
#z3 -smt2 insertion-sort.smt
#echo "checking propositional-logic..."
#z3 -smt2 propositional-logic.smt
#echo "checking quick-sort..."
#z3 -smt2 quick-sort.smt
#echo "checking lefist-heap..."
#z3 -smt2 leftist-heap.smt
#echo "checking heap-sort..."
#z3 -smt2 heap-sort.smt
#echo "checking binary-trie..."
#z3 -smt2 binary-trie.smt
#echo "checking AVL-tree..."
#z3 -smt2 AVL-tree.smt
#echo "checking red-black-tree..."
#z3 -smt2 red-black-tree.smt
