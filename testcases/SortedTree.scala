import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object SortedTree {
  sealed abstract class Tree
  case class Node(v: Int, left: Tree, right: Tree) extends Tree
  case class Leaf() extends Tree

  def depth(t: Tree) : Int = (t match {
      case Leaf() => 0
      case Node(_, l, r) =>
        if (depth(l) > depth(r)) {
          depth(l)+1
        } else {
          depth(r)+1
        }
  }) ensuring(res => res >= 0)

  def size(t: Tree) : Int = (t match {
      case Leaf() => 0
      case Node(_, l, r) => 1 + size(l) + size(r)
  }) ensuring(res => res >= 0)

  def content(t: Tree): Set[Int] = t match {
    case Leaf() => Set()
    case Node(v, l, r) => Set(v) ++ content(l) ++ content(r)
  }

  @induct
  def sizeDepthLemma(t: Tree) = (
    (depth(t) <= size(t))
  ).holds

  def isMostlySorted(t: Tree): Boolean = (t match {
    case Node(v, l @ Node(v1, l1, r1), r @ Node(v2, l2, r2)) =>
      isMostlySorted(l) &&
      isMostlySorted(r) &&
      v1 < v &&
      v2 > v
    case Node(v, Leaf(), r @ Node(v2, l2, r2)) =>
      isMostlySorted(r) &&
      v2 > v
    case Node(v, l @ Node(v1, l1, r1), Leaf()) =>
      isMostlySorted(l) &&
      v1 < v
    case _ => true
  })

  def isSortedMinMax(t: Tree, min: Int, max: Int): Boolean = (t match {
    case Node(v, l, r) =>
      isSortedMinMax(l, min, v) &&
      isSortedMinMax(r, v, max) &&
      v < max &&
      v > min
    case _ => true
  }) ensuring ( res => !res || (allGreaterThan(t, min) && allSmallerThan(t, max)))

  def isSortedMin(t: Tree, min: Int): Boolean = (t match {
    case Node(v, l, r) =>
      isSortedMinMax(l, min, v) &&
      isSortedMin(r, v) &&
      v > min
    case _ => true
  }) ensuring ( res => !res || allGreaterThan(t, min))

  def isSortedMax(t: Tree, max: Int): Boolean = (t match {
    case Node(v, l, r) =>
      isSortedMax(l, v) &&
      isSortedMinMax(r, v, max) &&
      v < max
    case _ => true
  }) ensuring ( res => !res || allSmallerThan(t, max))

  def isSorted(t: Tree): Boolean = (t match {
    case Node(v, l, r) =>
      isSortedMin(r, v) &&
      isSortedMax(l, v)
    case _ => true
  }) ensuring ( res => !res || (t match {
    case Node(v, l, r) =>
      isSorted(l) &&
      isSorted(r)
    case Leaf() => true
  }))

  def allSmallerThan(t: Tree, max: Int): Boolean = (t match {
      case Node(v, l, r) =>
        allSmallerThan(l, max) &&
        allSmallerThan(r, max) &&
        v < max
      case Leaf() => true
  })

  def allGreaterThan(t: Tree, min: Int): Boolean = (t match {
      case Node(v, l, r) =>
        allGreaterThan(l, min) &&
        allGreaterThan(r, min) &&
        v > min
      case Leaf() => true
  })

  @induct
  def sortedLemma1(t: Tree) = ({
    require(isSorted(t))

    t match {
      case Node(v, l, r) =>
        allGreaterThan(r, v) &&
        allSmallerThan(l, v)
      case Leaf() => true
    }
  }).holds

  //
  // OPERATIONS:
  //

  def insert1(t: Tree, newV: Int): Tree = (t match {
    case Leaf() => Node(newV, Leaf(), Leaf())
    case Node(v, l, r) => Node(v, insert1(l, newV), r)
  }) ensuring(res => content(res) == content(t) ++ Set(newV))

  def insert2(t: Tree, newV: Int): Tree = (t match {
    case Leaf() => Node(newV, Leaf(), Leaf())
    case Node(v, l, r) =>
      if (v == newV)
        t
      else
        Node(v, insert2(l, newV), r)
  }) ensuring(res => content(res) == content(t) ++ Set(newV))

  def insert3(t: Tree, newV: Int): Tree = (t match {
    case Leaf() => Node(newV, Leaf(), Leaf())
    case Node(v, l, r) =>
      if (v == newV)
        t
      else if (newV > v)
        Node(v, l, insert3(r, newV))
      else
        Node(v, insert3(l, newV), r)
  }) ensuring(res => content(res) == content(t) ++ Set(newV) && ((content(t) contains newV) || (size(res) > size(t))))

  def insert4(t: Tree, newV: Int): Tree = {
    require(isMostlySorted(t));

    (t match {
      case Leaf() => Node(newV, Leaf(), Leaf())
      case Node(v, l, r) =>
        if (v == newV)
          t
        else if (newV > v)
          Node(v, l, insert4(r, newV))
        else
          Node(v, insert4(l, newV), r)
    })} ensuring(res => content(res) == content(t) ++ Set(newV) && ((content(t) contains newV) || (size(res) > size(t))) && isMostlySorted(res))

  def contains1(t: Tree, searchV: Int): Boolean = (t match {
    case Leaf() => false
    case Node(v, l, r) =>
      (v == searchV) ||
      contains1(l, searchV) ||
      contains1(r, searchV)
  }) ensuring(_ == (content(t) contains searchV))

  def contains2(t: Tree, searchV: Int): Boolean = {
    require(isMostlySorted(t))

    (t match {
      case Leaf() => false
      case Node(v, l, r) =>
        if (searchV > v) {
          contains2(r, searchV)
        } else if (searchV < v) {
          contains2(l, searchV)
        } else {
          true
        }
  })} ensuring(_ == (content(t) contains searchV))

  def contains3(t: Tree, searchV: Int): Boolean = {
    require(isSorted(t))

    (t match {
      case Leaf() => false
      case Node(v, l, r) =>
        if (searchV > v) {
          contains3(r, searchV)
        } else if (searchV < v) {
          contains3(l, searchV)
        } else {
          true
        }
  })} ensuring(_ == (content(t) contains searchV))
}
