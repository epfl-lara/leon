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

  def isSorted(tree: Tree): Boolean = tree match {
    case Leaf() => true
    case Node(Leaf(), v, Leaf()) => true
    case Node(l@Node(_, vIn, _), v, Leaf()) => v > vIn && isSorted(l)
    case Node(Leaf(), v, r@Node(_, vIn, _)) => v < vIn && isSorted(r)
    case Node(l@Node(_, vInLeft, _), v, r@Node(_, vInRight, _)) =>
      v > vInLeft && v < vInRight && isSorted(l) && isSorted(r)
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

  def goodMember(tree: Tree, value: Int): Boolean = {
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
  } ensuring (_ || !(contents(tree) == contents(tree) ++ Set(value)))

  def badMember(tree: Tree, value: Int): Boolean = {
    require(isSorted(tree))
    tree match {
      case Leaf() => false
      case n @ Node(l, v, r) => if (v <= value) {
        member(r, value)
      } else if (v > value) {
        member(l, value)
      } else {
        true
      }
    }
  } ensuring (_ || !(contents(tree) == contents(tree) ++ Set(value)))

}

