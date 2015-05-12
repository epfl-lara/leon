import leon.invariant._
import leon.instrumentation._
import leon.annotation._

object LeftistHeap {
  sealed abstract class List
  case class Cons(head:BigInt,tail:List) extends List
  case class Nil() extends List

  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk : BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

  private def rightHeight(h: Heap) : BigInt = h match {
    case Leaf() => 0
    case Node(_,_,_,r) => rightHeight(r) + 1
  }

  private def rank(h: Heap) : BigInt = h match {
    case Leaf() => 0
    case Node(rk,_,_,_) => rk
  }

  private def hasLeftistProperty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rightHeight(l) >= rightHeight(r) && (rank(h) == rightHeight(h))
  })

  @monotonic
  def twopower(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x < 1) 1
    else
      2* twopower(x - 1)
  }

  def heapSize(t: Heap): BigInt = {
    require(hasLeftistProperty(t))
    (t match {
      case Leaf() => 0
      case Node(_,v, l, r) => heapSize(l) + 1 + heapSize(r)
    })
  } ensuring (res => tmpl((a,b) => twopower(rightHeight(t)) <= a*res + b)/* _ >= 0*/)

  def leftRightHeight(h: Heap) : BigInt = {h match {
    case Leaf() => 0
    case Node(_,_,l,r) => rightHeight(l)
  }}

  def listSize(l : List) : BigInt = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + listSize(xs)
  }) ensuring(_ >= 0)

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring(res => /*hasLeftistProperty(res)*/ /*&& (if (h != Leaf()) heapSize(res) == heapSize(h) - 1 else true) &&*/ tmpl((a,b) => time <= a*leftRightHeight(h) + b))

  private def merge(h1: Heap, h2: Heap) : Heap = {
    require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
    h1 match {
      case Leaf() => h2
      case Node(_, v1, l1, r1) => h2 match {
        case Leaf() => h1
        case Node(_, v2, l2, r2) =>
          if(v1 > v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring(res => hasLeftistProperty(res) && tmpl((a,b,c) => time <= a*rightHeight(h1) + b*rightHeight(h2) + c))

  private def makeT(value: BigInt, left: Heap, right: Heap) : Heap = {
    if(rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

  def insert(element: BigInt, heap: Heap) : Heap = {
    require(hasLeftistProperty(heap))
    merge(Node(1, element, Leaf(), Leaf()), heap)
  } ensuring(res => hasLeftistProperty(res) && tmpl((a,b,c) => time <= a*rightHeight(heap) + c))

  /*def buildHeap(l : List, h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    l match {
      case Nil() => h
      case Cons(x,xs) => buildHeap(xs, insert(x, h))
    }
  } ensuring(res => hasLeftistProperty(res) && heapSize(h) + listSize(l) == heapSize(res) tmpl((a, b, c) => nonRecTime <= a*rightHeight(h) + b && rec <= listSize(l) + c))

  def findMax(h: Heap) : BigInt = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,m,_,_) => m
      case Leaf() => -1000
    }
  }

  def removeElements(h : Heap, l : List) : List = {
    require(hasLeftistProperty(h))
    h match {
      case Leaf() => l
      case _ => removeElements(removeMax(h),Cons(findMax(h),l))
    }
  }*/ //ensuring(res => /*heapSize(h) + listSize(l) == listSize(res)*/ tmpl((a, b, c) => nonRecTime <= a*leftRightHeight(h) + b /*&& rec <= heapSize(h) + c*/))
}
