package plugin

import funcheck.lib.Specs._
import scala.collection.immutable._

/**
 * Example adapted from book "Purely Functional Data Structures"
 * by Chris Okasaki.
 */ 
  
object LeftistHeap extends Application {
  
  /** method used for specification */
  def min(xs: List[Elem]): Elem = {
    def inner(xs: List[Elem], local: Elem): Elem = xs match {
      case Nil => local
      case head :: tail =>
        if(leq(local,head))
          inner(tail,local)
        else
          inner(tail,head)
    }
    inner(xs,Elem(Integer.MAX_VALUE))
  }
  
  /** method used for specification */
  def content(t : Heap): Multiset[Elem] = {
    def inner(t: Heap, mset: Multiset[Elem]): Multiset[Elem] = t match {
      case E() => mset
      case T(rank,el,left,right) => inner(right, inner(left, mset +++ List(el)))
    }
    inner(t,Multiset.empty[Elem])
  }
  
  /** class hierarchy */
  sealed abstract class Heap
  case class T(val rank: Int, val el: Elem, val left: Heap,val right: Heap) extends Heap
  @generator case class E() extends Heap
  
  @generator case class Elem(val value: Int) 

  def leq(e1: Elem, e2: Elem): Boolean =  e1.value <= e2.value
  
  /** mege the current heap <code>this</code> with the <code>that</code> */
  def merge(thiz: Heap, that: Heap): Heap = thiz match {
    case E() => that
    case T(_,x,a1,b1) => that match {
      case E() => thiz
      case T(_,y,_,_) if leq(x,y) =>
        makeT(a1, x, merge(b1, that))
      case T(_,y,a2,b2) if !leq(x,y) =>
        makeT(a2, y, merge(thiz, b2))
    }
  }
  
  /** helper function that calculates the rank of a <code>T</code> node
   *  and swaps its children if necessary. */ 
  def makeT(thiz: Heap, x: Elem, that: Heap): Heap = { 
    if(rankk(thiz) >= rankk(that)) {
      T(rankk(that) + 1, x, thiz, that)
    } else {
      T(rankk(thiz) + 1, x, that, thiz)
    }
  } 
  
  /** find the rank of a heap */
  def rankk(thiz: Heap): Int = thiz match {
    case E() => 0
    case T(rank,_,_,_) => rank
  }

  /** insert an element in the current heap <code>this</code>*/
  @generator
  def insert(thiz: Heap, x: Elem): Heap = merge(thiz, T(1,x,E(),E()))
  
  /** Find the smallest element of the current heap <code>this</code>. 
   *  Invariant on this data structure entails that the minimum is at the root.
   */ 
  def findMin(thiz: Heap): Elem = thiz match {
    case E() => error(toString())
    case T(_,x,_,_) => x
  }

  /** Delete the smallest element of the current heap <code>this</code>.
   *  Invariant on this data structure entails that the minimum is at the root.
   */
  def deleteMin(thiz: Heap): Heap = thiz match {
    case E() => Predef.error(toString())
    case T(_,_,a: Heap,b: Heap) => merge(a,b)
  }
  
  
  /** global invariants */
  //val heapMerge = forAll( (thiz: Heap, that: Heap) => content(thiz.merge(that)).equals(content(thiz) +++ content(that)))
  forAll[(Heap,Heap)] (heaps => content(merge(heaps._1,heaps._2)).equals(content(heaps._1) +++ content(heaps._2)))

  
  //val heapInsert = forAll( (heap: Heap, value: Elem) => content(heap.insert(value))(value) == content(heap)(value) + 1)
  forAll[(Heap,Elem)]( p => content(insert(p._1,p._2))(p._2) == content(p._1)(p._2) + 1)
  
    
  //val heapFindMin = forAll{ heap : Heap => (heap.rankk > 0) ==> (heap.findMin == min(content(heap).elements.toList))}
  //forAll{ heap : Heap => (rankk(heap) > 0) ==> (heap.findMin == min(content(heap).elements.toList))}
  
  
  
  //val heapDeleteMin = forAll{ heap: Heap => (heap.rankk > 0) ==> (content(heap.deleteMin).equals(content(heap) - heap.findMin))}
  //forAll{ heap: Heap => (heap.rankk > 0) ==> (content(heap.deleteMin).equals(content(heap) - heap.findMin))}
}

