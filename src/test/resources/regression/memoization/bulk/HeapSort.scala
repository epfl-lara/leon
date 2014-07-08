/* Copyright 2009-2013 EPFL, Lausanne
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
  case class Node(value: Int, left: Heap, right: Heap) extends Heap

  //O(logn) assuming leftist
  private def rank(h: Heap) : Int = h match {
    case Leaf() => 0
    case Node(_,_,r) => rank(r) + 1
  }

  // O(nlogn) -- will be called on each node once
  private def hasLeftistProperty(h: Heap) : Boolean = h match {
    case Leaf() => true
    case Node(_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rank(l) >= rank(r)
  }

  // O(n^2logn)
  def heapSize(t: Heap): Int = {
    require(hasLeftistProperty(t))
    (t match {
      case Leaf() => 0
      case Node(v, l, r) => heapSize(l) + 1 + heapSize(r)
    })
  } ensuring(_ >= 0)

  // O(n^2logn) + T(n/2)
  // O(n^2logn)
  private def merge(h1: Heap, h2: Heap) : Heap = {
    require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
    h1 match {
      case Leaf() => h2
      case Node( v1, l1, r1) => h2 match {
        case Leaf() => h1
        case Node( v2, l2, r2) =>
          if(v1 > v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring(res => hasLeftistProperty(res) && heapSize(h1) + heapSize(h2) == heapSize(res))

  // O(logn)
  private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
    if(rank(left) >= rank(right))
      Node(value, left, right)
    else
      Node(value, right, left)
  }

  // O(n^2logn)
  def insert(element: Int, heap: Heap) : Heap = {
    require(hasLeftistProperty(heap))

    merge(Node(element, Leaf(), Leaf()), heap)

  } ensuring(res => heapSize(res) == heapSize(heap) + 1)

  // O(nlogn)
  def findMax(h: Heap) : Int = {
    require(hasLeftistProperty(h))
    h match {
      case Node(m,_,_) => m
      case Leaf() => -1000
    }
  }

  // O(n^2logn)
  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  }

  def listSize(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + listSize(xs)
  }) ensuring(_ >= 0)

  // O(n^3logn)
  def removeElements(h : Heap, l : List) : List = {
   require(hasLeftistProperty(h))
   h match {
    case Leaf() => l
    case _ => removeElements(removeMax(h),Cons(findMax(h),l))

  }} ensuring(res => heapSize(h) + listSize(l) == listSize(res))

  // O(n^2logn) for each node
  // O(n^3logn)
  def buildHeap(l : List, h: Heap) : Heap = {
   require(hasLeftistProperty(h))
   l match {
    case Nil() => h
    case Cons(x,xs) => buildHeap(xs, insert(x, h))

  }} ensuring(res => hasLeftistProperty(res) && heapSize(h) + listSize(l) == heapSize(res))

  // O(n^3logn)
  def sort(l: List): List = ({

    val heap = buildHeap(l,Leaf())
    removeElements(heap, Nil())

  }) ensuring(res => listSize(res) == listSize(l))

  /*
  // pseudorandom els. to insert
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : List) : List = {
    if (size == 0) acc
    else rec(size -1, Cons(psr(size),acc))
  }
  
  def test(size : Int) : List = { 
      val l = rec(size, Nil())
      sort(l)
  }
*/
  
  def init() : List = Nil()
  def simpleInsert(l : List, i : Int) = Cons(i,l)
  def test(l : List) : List = sort(l)

}
