import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case class Leaf() extends Tree

  def content(t : Tree): Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
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

  def deleteSynth(in : Tree, v : Int) = choose {
    (out : Tree) => content(out) == (content(in) -- Set(v))
  }

  def insertSynth(in : Tree, v : Int) = choose {
    (out : Tree) => content(out) == (content(in) ++ Set(v))
  }

  def insertSortedSynth(in : Tree, v : Int) = choose {
    (out : Tree) => isSorted(in) && (content(out) == (content(in) ++ Set(v))) && isSorted(out)
  }

  def deleteSortedSynth(in : Tree, v : Int) = choose {
    (out : Tree) => isSorted(in) && (content(out) == (content(in) -- Set(v))) && isSorted(out)
  }
}
