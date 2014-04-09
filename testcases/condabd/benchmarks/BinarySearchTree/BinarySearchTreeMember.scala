import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinarySearchTree {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def contents(tree: Tree): Set[Int] = tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => contents(l) ++ Set(v) ++ contents(r)
  }
//  def isSorted(tree: Tree): Boolean = tree match {
//    case Leaf() => true
//    case Node(Leaf(), v, Leaf()) => true
//    case Node(l@Node(_, vIn, _), v, Leaf()) => v > vIn && isSorted(l)
//    case Node(Leaf(), v, r@Node(_, vIn, _)) => v < vIn && isSorted(r)
//    case Node(l@Node(_, vInLeft, _), v, r@Node(_, vInRight, _)) =>
//      v > vInLeft && v < vInRight && isSorted(l) && isSorted(r)
//  }
//  

  def isSorted(tree: Tree): Boolean =
    isSortedMaxMin(tree, Int.MinValue, Int.MaxValue)  
    
  def max(a: Int, b: Int) = if (a < b) b else a
  
  def min(a: Int, b: Int) = if (a > b) b else a
  
  def isSortedMaxMin(tree: Tree, minVal: Int, maxVal: Int): Boolean = tree match {
    case Leaf() => true    
    case Node(left, v, right) =>
      minVal < v && v < maxVal &&
      // go left, update upper bound
      isSortedMaxMin(left, minVal, min(maxVal, v)) &&
      isSortedMaxMin(right, max(minVal, v), maxVal)
  }
  
  def member(tree: Tree, value: Int): Boolean = {
    require(isSorted(tree))
    choose {
      (res: Boolean) =>
        (
            if (res) (contents(tree) == contents(tree) ++ Set(value))
            else !(contents(tree) == contents(tree) ++ Set(value))
        )
    }
  }

//  def member(tree: Tree, value: Int): Boolean = {
//    require(isSorted(tree))
//    tree match {
//      case Leaf() => false
//      case n @ Node(l, v, r) => if (v < value) {
//        member(r, value)
//      } else if (v > value) {
//        member(l, value)
//      } else {
//        true
//      }
//    }
//  } ensuring (_ || !(contents(tree) == contents(tree) ++ Set(value)))
//
//  def insert(tree: Tree, value: Int): Node = {
//    require(isSorted(tree))
//    tree match {
//      case Leaf() => Node(Leaf(), value, Leaf())
//      case n @ Node(l, v, r) => if (v < value) {
//        Node(l, v, insert(r, value))
//      } else if (v > value) {
//        Node(insert(l, value), v, r)
//      } else {
//        n
//      }
//    }
//  } ensuring (res => contents(res) == contents(tree) ++ Set(value) && isSorted(res))

  //  def treeMin(tree: Node): Int = {
  //    require(isSorted(tree).sorted)
  //    tree match {
  //      case Node(left, v, _) => left match {
  //        case Leaf() => v
  //        case n@Node(_, _, _) => treeMin(n)
  //      }
  //    }
  //  }
  //
  //  def treeMax(tree: Node): Int = {
  //    require(isSorted(tree).sorted)
  //    tree match {
  //      case Node(_, v, right) => right match {
  //        case Leaf() => v
  //        case n@Node(_, _, _) => treeMax(n)
  //      }
  //    }
  //  }
  
//  def remove(tree: Tree, value: Int): Node = {
//    require(isSorted(tree))
//    tree match {
//      case l @ Leaf() => l
//      case n @ Node(l, v, r) => if (v < value) {
//        Node(l, v, insert(r, value))
//      } else if (v > value) {
//        Node(insert(l, value), v, r)
//      } else {
//        n
//      }
//    }
//  } ensuring (contents(_) == contents(tree) -- Set(value))

}

