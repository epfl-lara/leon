import scala.collection.immutable.Set
import leon.invariant._
import leon.instrumentation._
import leon.annotation._
import leon.lang._

object HeapSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

  @monotonic
  def log(x: BigInt): BigInt = {
    require(x >= 0)
    if (x <= 1) 0
    else {
      1 + log(x / 2)
    }
  } ensuring (_ >= 0)

  // @library
  // def logMonotone(x: BigInt, y: BigInt) = {
  //   require(x >= 0 && y >=0 )
  //   if(x <= y) log(x) <= log(y)
  //   else log(x) >= log(y)
  // } holds

  @library
  def heapSize(t: Heap): BigInt = {
    require(hasLeftistProperty(t))
    t match {
      case Leaf() => 0
      case Node(_, v, l, r) => heapSize(l) + 1 + heapSize(r)
    }
  } ensuring (res => res >= 0 && rightHeight(t) <= log(res) + 1)

  private def rightHeight(h: Heap): BigInt = {
    h match {
      case Leaf() => 0
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (res => res >= 0)

  private def rank(h: Heap): BigInt = h match {
    case Leaf() => 0
    case Node(rk, _, _, _) => rk
  }

  private def hasLeftistProperty(h: Heap): Boolean = (h match {
    case Leaf() => true
    case Node(_, _, l, r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rightHeight(l) >= rightHeight(r) && (rank(h) == rightHeight(h))
  })

  def leftRightHeight(h: Heap): BigInt = {
    h match {
      case Leaf() => 0
      case Node(_, _, l, r) => rightHeight(l)
    }
  }

  // @library
  private def merge(h1: Heap, h2: Heap): Heap = {
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
  } ensuring (res => hasLeftistProperty(res) && heapSize(res) == heapSize(h1) + heapSize(h2) &&
      //time <= ? * rightHeight(h1) + ? * rightHeight(h2) + ? )
		  time <= 35*rightHeight(h1) + 35*rightHeight(h2) + 2)

  private def makeT(value: BigInt, left: Heap, right: Heap): Heap = {
    require(hasLeftistProperty(left) && hasLeftistProperty(right))
    if (rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

  // @library
  def insert(element: BigInt, heap: Heap): Heap = {
    require(hasLeftistProperty(heap))

    merge(Node(1, element, Leaf(), Leaf()), heap)

  } ensuring(res => heapSize(res) == heapSize(heap) + 1 &&
      time <= 35*rightHeight(heap) + 41)

  // def findMax(h: Heap) : BigInt = {
  //   require(hasLeftistProperty(h))
  //   h match {
  //     case Node(_,m,_,_) => m
  //     case Leaf() => -1000
  //   }
  // }

  // def removeMax(h: Heap) : Heap = {
  //   require(hasLeftistProperty(h))
  //   h match {
  //     case Node(_,_,l,r) => merge(l, r)
  //     case l @ Leaf() => l
  //   }
  // } ensuring(res => true && tmpl((a,b) => time <= a*leftRightHeight(h) + b))

  // def listSize(l: List): BigInt = (l match {
  //   case Nil() => 0
  //   case Cons(_, xs) => 1 + listSize(xs)
  // }) ensuring (_ >= 0)

  // def removeElements(h : Heap, l : List) : List = {
  //   require(hasLeftistProperty(h))
  //   h match {
  //     case Leaf() => l
  //     case _ => removeElements(removeMax(h),Cons(findMax(h),l))
  //   }
  // } ensuring(res => heapSize(h) + listSize(l) == listSize(res))

  // @compose
  // def buildHeap(l: List, h: Heap): Heap = {
  //   require(hasLeftistProperty(h))
  //   l match {
  //     case Nil() => h
  //     case Cons(x, xs) => buildHeap(xs, insert(x, h))
  //   }
  // } ensuring (res => hasLeftistProperty(res) &&
  //     heapSize(res) >= heapSize(h) &&
  //     logMonotone(heapSize(h), heapSize(res)) &&
  //     tpr <= ? * log(heapSize(res)) + ? &&
  //     rec <= ? * listSize(l) + ? &&
  //     time <= ? *(listSize(l)*log(heapSize(res))) + ? *log(heapSize(res)) + ?)

  // def sort(l: List): List = ({
  //   val heap = buildHeap(l,Leaf())
  //   removeElements(heap, Nil())
  // }) ensuring(res => listSize(res) == listSize(l))
}