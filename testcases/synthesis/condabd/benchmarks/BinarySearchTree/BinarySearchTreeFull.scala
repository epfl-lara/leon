
import leon.annotation._
import leon.lang._

object BinarySearchTree {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def contents(tree: Tree): Set[Int] = tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => contents(l) ++ Set(v) ++ contents(r)
  }

  def isSortedMinMax(t: Tree, min: Int, max: Int): Boolean = t match {
    case Node(l, v, r) =>
      isSortedMinMax(l, min, v) &&
      isSortedMinMax(r, v, max) &&
      v < max && v > min
    case _ => true
  }

  def isSortedMin(t: Tree, min: Int): Boolean = t match {
    case Node(l, v, r) =>
      isSortedMinMax(l, min, v) &&
      isSortedMin(r, v) &&
      v > min
    case _ => true
  }

  def isSortedMax(t: Tree, max: Int): Boolean = t match {
    case Node(l, v, r) =>
      isSortedMax(l, v) &&
      isSortedMinMax(r, v, max) &&
      v < max
    case _ => true
  }

  def isSorted(t: Tree): Boolean = t match {
    case Node(l, v, r) =>
      isSortedMin(r, v) &&
      isSortedMax(l, v)
    case _ => true
  }
  
//  def isSorted(tree: Tree): Boolean = tree match {
//    case Leaf() => true
//    case Node(Leaf(), v, Leaf()) => true
//    case Node(l @ Node(_, vIn, _), v, Leaf()) => v > vIn && isSorted(l)
//    case Node(Leaf(), v, r @ Node(_, vIn, _)) => v < vIn && isSorted(r)
//    case Node(l @ Node(_, vInLeft, _), v, r @ Node(_, vInRight, _)) =>
//      v > vInLeft && v < vInRight && isSorted(l) && isSorted(r)
//  }
//  
//  def isSorted(tree: Tree): Boolean = tree match {
//    case Leaf() => true
//    case Node(l, v, r) => isLowerThan(l, v) && isGreaterThan(r, v) && isSorted(l) && isSorted(r)   
//  }
//  
//  def isLowerThan(tree: Tree, max: Int): Boolean = tree match {
//    case Leaf() => true
//    case Node(l, v, r) => v < max && isLowerThan(l, max) && isLowerThan(r, max)
//  }
//  
//  def isGreaterThan(tree: Tree, min: Int): Boolean = tree match {
//    case Leaf() => true
//    case Node(l, v, r) => v > min && isGreaterThan(r, min) && isGreaterThan(l, min) 
//  }
//  
//  def isSorted(tree: Tree): Boolean = tree match {
//    case Leaf() => true
//    case Node(l, v, r) => isSorted(l) && isSorted(r) &&
//    	contents(l).forall( v > _ ) && contents(r).forall( v < _ )
//  }

  def member(tree: Tree, value: Int): Boolean = {
    require(isSorted(tree))
    tree match {
      case Leaf() => false
      case n @ Node(l, v, r) => if (v < value) {
        member(r, value)
      } else if (v > value) {
        member(l, value)
      } else {
        true
      }
    }
  } ensuring (res =>
    (res && contents(tree).contains(value)) ||
    (!res && !contents(tree).contains(value))
  )

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
//    require(isSorted(tree))
//    tree match {
//      case Node(left, v, _) => left match {
//        case Leaf() => v
//        case n @ Node(_, _, _) => treeMin(n)
//      }
//    }
//  }
//
//  def treeMax(tree: Node): Int = {
//    require(isSorted(tree))
//    tree match {
//      case Node(_, v, right) => right match {
//        case Leaf() => v
//        case n @ Node(_, _, _) => treeMax(n)
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
//  } ensuring (res => contents(res) == contents(tree) -- Set(value))

}

