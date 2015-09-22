/*
Case study by Ravichandhran Kandhadai Madhavan, 2015
Confirmed verified on 2015-09-22 using 
   --solvers=smt-z3 --timeout=15  
*/
import leon.lang._
import leon.annotation._
import leon.collection._

object BinaryTree {
  sealed abstract class Tree {
    /**
     * Returns the contents of the tree in preorder
     */
    def toList: List[BigInt] = {
      this match {
        case Node(l, v, r) =>
          (l.toList ++ sing(v)) ++ r.toList
        case _ =>
          Nil[BigInt]()
      }
    } ensuring (res => this == Leaf() || res != Nil[BigInt]())
    
    def toSet: Set[BigInt] = {
      this match {
        case Node(l, v, r) =>
          l.toSet ++ Set(v) ++ r.toSet
        case _ =>
          Set[BigInt]()
      }
    } ensuring (res => this == Leaf() || res != Set[BigInt]())
    
  }
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree 
  case class Leaf() extends Tree

  def BST(t: Tree): Boolean = t match {
    case Leaf() => true
    case Node(l, v, r) =>
      BST(l) && BST(r) && isSorted(t.toList) &&
        (l.toList == Nil[BigInt]() || l.toList.last < v) &&
        (r.toList == Nil[BigInt]() || v < first(r.toList))
  }

  def sing(x: BigInt): List[BigInt] = {
    Cons[BigInt](x, Nil[BigInt]())
  }

  def min(x: BigInt, y: BigInt): BigInt = {
    if (x <= y) x else y
  }

  def max(x: BigInt, y: BigInt): BigInt = {
    if (x >= y) x else y
  }

  def insert(tree: Tree, value: BigInt): Tree = ({
    require(BST(tree))
    tree match {
      case Leaf() => 
        Node(Leaf(), value, Leaf())
      case Node(l, v, r) => if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        Node(l, v, r)
      }
    }
  }) ensuring (res => BST(res) &&
    res.toSet == tree.toSet ++ Set(value) &&
    res.toList != Nil[BigInt]() &&
    (tree match {
      case Leaf() => (first(res.toList) == value) &&
        (res.toList.last == value)
      case _ =>
        first(res.toList) == min(first(tree.toList), value) &&
          res.toList.last == max(tree.toList.last, value)
    })
    &&
    instAppendSorted(tree, value))

  def instAppendSorted(t: Tree, value: BigInt): Boolean = {
    require(BST(t))
    t match {
      case Leaf() =>
        true
      case Node(l, v, r) =>
        appendSorted(l.toList, sing(v)) &&
          appendSorted(l.toList ++ sing(v), r.toList) &&
          (if (v < value) {
            appendSorted(l.toList, sing(v)) &&
              appendSorted(l.toList ++ sing(v), insert(r, value).toList)
          } else if (v > value) {
            appendSorted(insert(l, value).toList, sing(v)) &&
              appendSorted(insert(l, value).toList ++ sing(v), r.toList)
          } else true)
    }
  }

  // this computes strict sortedness
  def isSorted(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, tail @ Cons(y, _)) =>
        (x < y) && isSorted(tail)
    }
  } ensuring (res => !res || l == Nil[BigInt]() || first(l) <= l.last)

  def first(l: List[BigInt]): BigInt = {
    require(l != Nil[BigInt])
    l match {
      case Cons(x, _) => x
    }
  }

  // A lemma about `append` and `isSorted`
  def appendSorted(l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(isSorted(l1) && isSorted(l2) &&
      (l1 == Nil[BigInt]() || l2 == Nil[BigInt]() || l1.last < first(l2)))
    // induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => appendSorted(xs, l2)
    }) &&
      (l1 == Nil[BigInt]() || first(l1 ++ l2) == first(l1)) &&
      (l2 == Nil[BigInt]() || (l1 ++ l2).last == l2.last) &&
      (l2 != Nil[BigInt]() || l1 == Nil[BigInt]() || (l1 ++ l2).last == l1.last) &&
      isSorted(l1 ++ l2)
  }.holds
}
