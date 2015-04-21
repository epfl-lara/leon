import leon.lang._
import leon.annotation._
import leon.collection._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  case class SortedTriple(min: Option[Int], max: Option[Int], sorted: Boolean)

  def isSortedTriple(tree: Tree) : SortedTriple = (tree match {
    case Leaf() => SortedTriple(None(), None(), true)
    case Node(l, v, r) =>
      (isSortedTriple(l), isSortedTriple(r)) match {
        case (SortedTriple(minl, maxl, sortedl), SortedTriple(minr, maxr, sortedr)) =>
          val sorted = sortedl && sortedr && (v > maxl.getOrElse(v-1)) && (v < minr.getOrElse(v+1))
          SortedTriple(minl.orElse(Some(v)), maxr.orElse(Some(v)), sorted)
      }
  }) ensuring { res => res match {
    case SortedTriple(Some(min), Some(max), res) => !res || (min <= max)
    case SortedTriple(None(), None(), res) => res
    case _ => false
  }}

  def isSorted(tree: Tree): Boolean = isSortedTriple(tree).sorted

  def insert(tree: Tree, value: Int): Tree = ({
    require(isSorted(tree))
    tree match {
      case Leaf() => Node(Leaf(), value, Leaf())
      case Node(l, v, r) => if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        Node(l,v,r)
      }
    }
  }) ensuring (res => isSorted(res))

  def buggyMerge(t1 : Tree, t2 : Tree) : Tree = ({
    require(isSorted(t1) && isSorted(t2))
    (t1, t2) match {
      case (Leaf(), _) => t2
      case (_, Leaf()) => t1
      case (t1 @ Node(l1, v1, r1), t2 @ Node(l2, v2, r2)) =>
        if (v1 < v2) {
          Node(buggyMerge(t1, l2), v2, r2)
        } else if (v2 < v1) {
          Node(buggyMerge(l1, t2), v1, r1)
        } else {
          Node(buggyMerge(l1, l2), v1, buggyMerge(r1, r2))
        }
    }
  }) ensuring (res => isSorted(res))
}
