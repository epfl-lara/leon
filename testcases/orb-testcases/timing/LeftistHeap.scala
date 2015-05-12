import leon.invariant._
import leon.instrumentation._
import leon.annotation._

object LeftistHeap {
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

  def size(t: Heap): BigInt = {
    require(hasLeftistProperty(t))
    (t match {
      case Leaf() => BigInt(0)
      case Node(_,v, l, r) => size(l) + 1 + size(r)
    })
  } ensuring (res => true && tmpl((a,b) => twopower(rightHeight(t)) <= a*res + b))

  def leftRightHeight(h: Heap) : BigInt = {h match {
    case Leaf() => 0
    case Node(_,_,l,r) => rightHeight(l)
  }}

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring(res => true && tmpl((a,b) => time <= a*leftRightHeight(h) + b))

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
  } ensuring(res => true && tmpl((a,b,c) => time <= a*rightHeight(h1) + b*rightHeight(h2) + c))

  private def makeT(value: BigInt, left: Heap, right: Heap) : Heap = {
    if(rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

  def insert(element: BigInt, heap: Heap) : Heap = {
   require(hasLeftistProperty(heap))

    merge(Node(1, element, Leaf(), Leaf()), heap)

  } ensuring(res => true && tmpl((a,b,c) => time <= a*rightHeight(heap) + c))
}
