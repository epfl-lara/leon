import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

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
    case Leaf() => Set.empty[Int]
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
      if(isSortedMinMax(l, min, v) &&
         isSortedMinMax(r, v, max) &&
         v < max && v > min) {
        ltLemma(l, v, max) &&
        gtLemma(r, v, min)
      } else false
    case _ => true
  }) ensuring ( _ == (allGreaterThan(t, min) && allLessThan(t, max) && isSorted(t)))

  def isSortedMin(t: Tree, min: Int): Boolean = (t match {
    case Node(v, l, r) =>
      if(isSortedMinMax(l, min, v) &&
         isSortedMin(r, v) &&
         v > min) {
        gtLemma(r, v, min)
      } else false
    case _ => true
  }) ensuring ( _ == (allGreaterThan(t, min) && isSorted(t)))

  def isSortedMax(t: Tree, max: Int): Boolean = (t match {
    case Node(v, l, r) =>
      if(isSortedMax(l, v) &&
         isSortedMinMax(r, v, max) &&
         v < max) {
        ltLemma(l, v, max)
      } else false
    case _ => true
  }) ensuring ( _ == (allLessThan(t, max) && isSorted(t)))

  def isSorted(t: Tree): Boolean = (t match {
    case Node(v, l, r) =>
      isSortedMin(r, v) &&
      isSortedMax(l, v)
    case _ => true
  }) ensuring ( res => !res || (t match {
    case Node(v, l, r) =>
      isSorted(l) &&
      isSorted(r) &&
      allLessThan(l, v) &&
      allGreaterThan(r, v) &&
      !(content(l) contains v) &&
      !(content(r) contains v)
    case Leaf() => true
  }))

  def sortedLemma(v : Int, l : Tree, r : Tree) : Boolean = {
    require(isSorted(l) && isSorted(r) && allLessThan(l, v) && allGreaterThan(r, v))
    isSorted(Node(v, l, r))
  } holds

  def allLessThan(t: Tree, max: Int): Boolean = (t match {
      case Node(v, l, r) =>
        allLessThan(l, max) &&
        allLessThan(r, max) &&
        v < max
      case Leaf() => true
  }) ensuring (!_ || !(content(t) contains max))

  def allGreaterThan(t: Tree, min: Int): Boolean = (t match {
      case Node(v, l, r) =>
        allGreaterThan(l, min) &&
        allGreaterThan(r, min) &&
        v > min
      case Leaf() => true
  }) ensuring (res => !res || !(content(t) contains min))

  @induct
  def ltLemma(t : Tree, v1 : Int, v2 : Int) : Boolean = {
    require(v1 <= v2 && allLessThan(t, v1))
    allLessThan(t, v2)
  } holds
  
  @induct
  def gtLemma(t : Tree, v1 : Int, v2 : Int) : Boolean = {
    require(v1 >= v2 && allGreaterThan(t, v1))
    allGreaterThan(t, v2)
  } holds

  @induct
  def sortedLemma1(t: Tree) = ({
    require(isSorted(t))

    t match {
      case Node(v, l, r) =>
        allGreaterThan(r, v) &&
        allLessThan(l, v)
      case Leaf() => true
    }
  }).holds

  @induct
  def sortedLemma2(t: Tree) = ({
    require(isSorted(t))

    t match {
      case Node(v, l, r) =>
        !(content(l) contains v) &&
        !(content(r) contains v)
      case Leaf() => true
    }
  }).holds

  def sortedLemma3(v: Int, l: Tree, r: Tree) = {
    require(isSorted(Node(v, l, r)))

    !((content(l) ++ content(r)) contains v)
  } holds

  // Proving is apparently difficult. Who knew.
  @induct
  def allLessThanAllOf(t: Tree, top: Int, of: Tree): Boolean = {
    require(isSorted(Node(top, t, of)))

    t match {
      case Node(v, l, r) =>
        top > v &&
        allLessThanAllOf(l, v, of) &&
        allLessThanAllOf(r, v, of) &&
        allGreaterThan(of, v)
      case Leaf() =>
        true
    }
  } ensuring {res => !res || (allLessThan(t, top) && allGreaterThan(of, top))}

  // Ne marche pas encore vraiment... c'est difficile ce truc :(
  // PS
  def separation(v : Int, l : Tree, r : Tree) : Boolean = {
    require(isSorted(Node(v, l, r)))
  
    (l match {
      case Leaf() => true
      case Node(vl, ll, rl) => separation(vl, ll, rl)
    }) && (r match {
      case Leaf() => true
      case Node(vr, lr, rr) => separation(vr, lr, rr)
    }) 
  } ensuring(res => !res || (content(l) ** content(r)) == Set.empty[Int])


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

  def containsInvalid(t: Tree, searchV: Int): Boolean = {
    require(isSorted(t))

    (t match {
      case Leaf() => false
      case Node(v, l, r) =>
        if (searchV > v) {
          containsInvalid(r, searchV)
        } else if (searchV < v) {
          containsInvalid(l, searchV)
        } else {
          true
        }
  })} ensuring(!_ || (content(t) contains searchV))

  def contains4(t: Tree, searchV: Int): Boolean = {
    require(isSorted(t))

    (t match {
      case Leaf() => false
      case Node(v, l, r) =>
        if (searchV > v) {
          contains4(r, searchV)
        } else if (searchV < v) {
          contains4(l, searchV)
        } else {
          true
        }
  })} ensuring(_ == (content(t) contains searchV))
}
