import leon.lang._
import leon.collection._

object HeapSort {
  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

  def rightHeight(h: Heap): BigInt = {
    h match {
      case Leaf() => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (_ >= 0)

  def rank(h: Heap): BigInt = h match {
    case Leaf() => 0
    case Node(rk, _, _, _) => rk
  }

  def max(x: BigInt, y: BigInt): BigInt = {
    if (x <= y) y else x
  }

  def rootVal(h: Heap): BigInt = {
    require(h != Leaf())
    h match {
      case Node(_, v, _, _) => v
    }
  }

  private def hasLeftistProperty(h: Heap): Boolean = (h match {
    case Leaf() => true
    case Node(_, v, l, r) => hasLeftistProperty(l) && hasLeftistProperty(r) &&
      // properties about rank (necessary for proving running time)
      rightHeight(l) >= rightHeight(r) && (rank(h) == rightHeight(h)) &&
      // properties of a max heap
      (l == Leaf() || v >= rootVal(l)) && (r == Leaf() || v >= rootVal(r))
  })

  def heapSize(t: Heap): BigInt = {
    (t match {
      case Leaf() => BigInt(0)
      case Node(_, v, l, r) => heapSize(l) + 1 + heapSize(r)
    })
  } ensuring (_ >= 0)

  def heapContents(t: Heap): Set[BigInt] = {
    t match {
      case Leaf() => Set()
      case Node(_, v, l, r) =>
        Set(v) ++ heapContents(l) ++ heapContents(r)
    }
  }

  def merge(h1: Heap, h2: Heap): Heap = {
    require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
    h1 match {
      case Leaf() => h2
      case Node(_, v1, l1, r1) => h2 match {
        case Leaf() => h1
        case Node(_, v2, l2, r2) =>
          if (v1 > v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring (res =>
    //the root value is one of the root values of the merged heaps
    (res match {
      case Leaf() => h1 == Leaf() && h2 == Leaf()
      case Node(_, v, _, _) =>
        (h1 != Leaf() && rootVal(h1) == v) || (h2 != Leaf() && rootVal(h2) == v)
    }) &&
      hasLeftistProperty(res) &&
      heapSize(h1) + heapSize(h2) == heapSize(res) &&
      heapContents(h1) ++ heapContents(h2) == heapContents(res))

  private def makeT(value: BigInt, left: Heap, right: Heap): Heap = {
    if (rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

  def insert(element: BigInt, heap: Heap): Heap = {
    require(hasLeftistProperty(heap))

    merge(Node(1, element, Leaf(), Leaf()), heap)

  } ensuring (res => heapSize(res) == heapSize(heap) + 1 &&
    heapContents(res) == Set(element) ++ heapContents(heap))

  def listMax(l: List[BigInt]): BigInt = {
    require(l != Nil[BigInt]())
    l match {
      case Cons(x, Nil()) =>
        x
      case Cons(x, tail) =>
        max(x, listMax(tail))
    }
  }

  def append(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    l1 match {
      case Nil() => l2
      case Cons(x, tail) =>
        Cons(x, append(tail, l2))
    }
  } ensuring (res => (l2 != Nil[BigInt]() || res == l1) &&
    (res == Nil[BigInt]() ||
      ((l1 == Nil[BigInt]() && listMax(res) == listMax(l2)) ||
        (l2 == Nil[BigInt]() && listMax(res) == listMax(l1)) ||
        (listMax(res) == max(listMax(l1), listMax(l2))))))

  def heapElements(t: Heap): List[BigInt] = {
    require(hasLeftistProperty(t))
    t match {
      case Leaf() => Nil[BigInt]()
      case Node(_, v, l, r) =>
        v :: append(heapElements(l), heapElements(r))
    }
  } ensuring (res => t == Leaf() ||
    (res != Nil[BigInt]() && rootVal(t) == listMax(res)))

  def findMax(h: Heap): BigInt = {
    require(hasLeftistProperty(h) && h != Leaf())
    rootVal(h)
  } ensuring (res => res == listMax(heapElements(h))) // max heap property

  def removeMax(h: Heap): Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_, _, l, r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring (res => hasLeftistProperty(res) &&
    (h == Leaf() || heapContents(h) == heapContents(res) ++ Set(findMax(h))) &&
    (res == Leaf() || findMax(res) <= findMax(h)))
}
