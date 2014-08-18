import scala.collection.immutable.Set

object LeftistHeap {
  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rank: Int, value: Int, left: Heap, right: Heap) extends Heap

  sealed abstract class HP
  case class HeapPair(heap1: Heap, heap2: Heap) extends HP

  private def rank(h: Heap) : Int = h match {
    case Leaf() => 0
    case Node(r,_,_,_) => r
  }

  def emptyHeap() : Heap = {
    Leaf()
  } ensuring(heapContent(_) == Set.empty[Int])

  def isHeapEmpty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,_,_,_) => false
  }) ensuring(_ == (heapContent(h) == Set.empty[Int]))

  private def hasLeftistProperty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,_,l,r) => rank(l) >= rank(r)
  })

  def heapContent(h: Heap) : Set[Int] = h match {
    case Leaf() => Set.empty[Int]
    case Node(_,v,l,r) => Set(v) ++ heapContent(l) ++ heapContent(r)
  }

  def findMax(h: Heap) : Int = {
    require(!isHeapEmpty(h) && hasLeftistProperty(h))
    h match {
      case Node(_,m,_,_) => m
      case Leaf() => -1000
    }
  } ensuring(_ == heapContent(h).max)

  def removeMax(h: Heap) : Heap = {
    require(!isHeapEmpty(h) && hasLeftistProperty(h))
    h match {
      case Node(_,_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring(res => {
      val cOld = heapContent(h)
      val cNew = heapContent(res)
      (cNew == Set.empty[Int] || cNew.max <= cOld.max) &&
      (cNew subsetOf cOld) &&
      (cOld.size - cNew.size <= 1) &&
      hasLeftistProperty(res)
    })

  //private def merge(h1: Heap, h2: Heap) : Heap = (HeapPair(h1, h2) match {
  //  case HeapPair(Leaf(), h2) => h2
  //  case HeapPair(h1, Leaf()) => h1
  //  case HeapPair(Node(_, v1, l1, r1), Node(_, v2, l2, r2)) =>
  //    if(v1 > v2)
  //      makeT(v1, l1, merge(r1, h2))
  //    else
  //      makeT(v2, l2, merge(h1, r2))
  //}) ensuring(heapContent(_) == heapContent(h1) ++ heapContent(h2))

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
  } ensuring(res => {
      (heapContent(res) == heapContent(h1) ++ heapContent(h2)) &&
      hasLeftistProperty(res)
    })

  private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
    if(rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  } ensuring(res => {
      heapContent(res) == Set(value) ++ heapContent(left) ++ heapContent(right) &&
      hasLeftistProperty(res)
    })

  def insert(element: Int, heap: Heap) : Heap = {
    merge(Node(1, element, Leaf(), Leaf()), heap)
  } ensuring(res => {
      val cNew = heapContent(res)
      val cOld = heapContent(heap)
      cNew == Set(element) ++ heapContent(heap) &&
      hasLeftistProperty(res)
    })

  def main(args: Array[String]) : Unit = {
    val h1 = emptyHeap()
    val h2 = insert(8, insert(0, insert(8, insert(24, insert(41, insert(13, h1))))))
    var h3 = h2
    while(!isHeapEmpty(h3)) {
      println(h3)
      println(findMax(h3))
      h3 = removeMax(h3)
    }
  }
}
