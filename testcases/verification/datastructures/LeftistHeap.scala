/* Copyright 2009-2015 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._

object LeftistHeap {
  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk : Int, value: Int, left: Heap, right: Heap) extends Heap

  private def rightHeight(h: Heap) : Int = {h match {
    case Leaf() => 0
    case Node(_,_,_,r) => rightHeight(r) + 1
  }} ensuring(_ >= 0)

  private def hasLeftistProperty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rightHeight(l) >= rightHeight(r)
  })

  def size(t: Heap): Int = {
    (t match {
      case Leaf() => 0
      case Node(_,v, l, r) => size(l) + 1 + size(r)
    })
  }

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring(res => size(res) >= size(h) - 1)

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
  } ensuring(res => size(res) == size(h1) + size(h2))

  private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
    if(rightHeight(left) >= rightHeight(right))
      Node(rightHeight(right) + 1, value, left, right)
    else
      Node(rightHeight(left) + 1, value, right, left)
  }

  def insert(element: Int, heap: Heap) : Heap = {
   require(hasLeftistProperty(heap))

    merge(Node(1, element, Leaf(), Leaf()), heap)

  }ensuring(res => size(res) == size(heap) + 1)
}
