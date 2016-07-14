/* Copyright 2009-2015 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._
import leon.collection._

object Heaps {
 
  sealed abstract class Heap {
    val rank : BigInt = this match {
      case Leaf() => 0
      case Node(_, l, r) => 
        1 + max(l.rank, r.rank)
    }
    def content : Set[BigInt] = this match {
      case Leaf() => Set[BigInt]()
      case Node(v,l,r) => l.content ++ Set(v) ++ r.content
    }
  }
  case class Leaf() extends Heap
  case class Node(value:BigInt, left: Heap, right: Heap) extends Heap

  def max(i1 : BigInt, i2 : BigInt) = if (i1 >= i2) i1 else i2

  def hasHeapProperty(h : Heap) : Boolean = h match {
    case Leaf() => true
    case Node(v, l, r) => 
      ( l match {
        case Leaf() => true
        case n@Node(v2,_,_) => v >= v2 && hasHeapProperty(n)
      }) && 
      ( r match {
        case Leaf() => true
        case n@Node(v2,_,_) => v >= v2 && hasHeapProperty(n)
      })
  }

  def hasLeftistProperty(h: Heap) : Boolean = h match {
    case Leaf() => true
    case Node(_,l,r) => 
      hasLeftistProperty(l) && 
      hasLeftistProperty(r) && 
      l.rank >= r.rank 
  }

  def heapSize(t: Heap): BigInt = { t match {
    case Leaf() => BigInt(0)
    case Node(v, l, r) => heapSize(l) + 1 + heapSize(r)
  }} ensuring(_ >= 0)

  def merge(h1: Heap, h2: Heap) : Heap = {
    require(
      hasLeftistProperty(h1) && hasLeftistProperty(h2) && 
      hasHeapProperty(h1) && hasHeapProperty(h2)
    )
    (h1,h2) match {
      case (Leaf(), _) => h2
      case (_, Leaf()) => h1
      case (Node(v1, l1, r1), Node(v2, l2, r2)) =>
        if(v1 >= v2) // FIXME swapped the branches
          makeN(v2, l2, merge(h1, r2))
        else
          makeN(v1, l1, merge(r1, h2))
    }
  } ensuring { res => 
    hasLeftistProperty(res) && hasHeapProperty(res) &&
    heapSize(h1) + heapSize(h2) == heapSize(res) &&
    h1.content ++ h2.content == res.content 
  }

  private def makeN(value: BigInt, left: Heap, right: Heap) : Heap = {
    require(
      hasLeftistProperty(left) && hasLeftistProperty(right)
    )
    if(left.rank >= right.rank)
      Node(value, left, right)
    else
      Node(value, right, left)
  } ensuring { res =>
    hasLeftistProperty(res)  }

  def insert(element: BigInt, heap: Heap) : Heap = {
    require(hasLeftistProperty(heap) && hasHeapProperty(heap))

    merge(Node(element, Leaf(), Leaf()), heap)

  } ensuring { res =>
    hasLeftistProperty(res) && hasHeapProperty(res) &&
    heapSize(res) == heapSize(heap) + 1 &&
    res.content == heap.content ++ Set(element)
  }

  def findMax(h: Heap) : Option[BigInt] = {
    h match {
      case Node(m,_,_) => Some(m)
      case Leaf() => None()
    }
  }

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h) && hasHeapProperty(h))
    h match {
      case Node(_,l,r) => merge(l, r)
      case l => l
    }
  } ensuring { res =>
    hasLeftistProperty(res) && hasHeapProperty(res)
  }

} 
