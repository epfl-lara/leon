/* Copyright 2009-2015 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._

object HeapSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk : Int, value: Int, left: Heap, right: Heap) extends Heap

  private def rightHeight(h: Heap) : Int = {h match {
    case Leaf() => 0
    case Node(_,_,_,r) => rightHeight(r) + 1
  }} ensuring(_ >= 0)

  private def rank(h: Heap) : Int = h match {
    case Leaf() => 0
    case Node(rk,_,_,_) => rk
  }

  private def hasLeftistProperty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rightHeight(l) >= rightHeight(r) && (rank(h) == rightHeight(h))
  })

  def heapSize(t: Heap): Int = {
    require(hasLeftistProperty(t))
    (t match {
      case Leaf() => 0
      case Node(_,v, l, r) => heapSize(l) + 1 + heapSize(r)
    })
  } ensuring(_ >= 0)

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
  } ensuring(res => hasLeftistProperty(res) && heapSize(h1) + heapSize(h2) == heapSize(res))


  private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
    if(rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

 def insert(element: Int, heap: Heap) : Heap = {
   require(hasLeftistProperty(heap))

    merge(Node(1, element, Leaf(), Leaf()), heap)

  } ensuring(res => heapSize(res) == heapSize(heap) + 1)

   def findMax(h: Heap) : Int = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,m,_,_) => m
      case Leaf() => -1000
    }
  }

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  }

  def listSize(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + listSize(xs)
  }) ensuring(_ >= 0)

  def removeElements(h : Heap, l : List) : List = {
          require(hasLeftistProperty(h))
   h match {
    case Leaf() => l
    case _ => removeElements(removeMax(h),Cons(findMax(h),l))

  }} ensuring(res => heapSize(h) + listSize(l) == listSize(res))

  def buildHeap(l : List, h: Heap) : Heap = {
          require(hasLeftistProperty(h))
   l match {
    case Nil() => h
    case Cons(x,xs) => buildHeap(xs, insert(x, h))

  }} ensuring(res => hasLeftistProperty(res) && heapSize(h) + listSize(l) == heapSize(res))

  def sort(l: List): List = ({

    val heap = buildHeap(l,Leaf())
    removeElements(heap, Nil())

  }) ensuring(res => listSize(res) == listSize(l))
}
