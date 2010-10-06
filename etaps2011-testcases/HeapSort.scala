import scala.collection.immutable.Set

object HeapSort {
  // This first part is concerned with simulating a heap
  sealed abstract class Heap
  case class DummyHeap(i: Int) extends Heap

  def emptyHeap() : Heap = {
    throw new Exception("Unimplemented")
    (DummyHeap(0) : Heap)
  } ensuring(heapContent(_) == Set.empty[Int])

  def isHeapEmpty(h: Heap) : Boolean = {
    throw new Exception("Unimplemented")
    false
  } ensuring(res => res == (heapContent(h) == Set.empty[Int]))

  def heapContent(h: Heap) : Set[Int] = {
    throw new Exception("Unimplemented")
    Set.empty[Int]
  }

  def findMax(h: Heap) : Int = {
    require(!isHeapEmpty(h))
    throw new Exception("Unimplemented")
    0
  } ensuring(_ == heapContent(h).max)

  def removeMax(h: Heap) : Heap = {
    require(!isHeapEmpty(h))
    throw new Exception("Unimplemented")
    (DummyHeap(0) : Heap)
  } ensuring(res => {
      val cOld = heapContent(h)
      val cNew = heapContent(res)
      (cNew == Set.empty[Int] || cNew.max <= cOld.max) &&
      (cNew subsetOf cOld) &&
      (cOld.size - cNew.size <= 1)
    })

  // The rest is concerned with heapsort
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def listContent(l: List) : Set[Int] = (l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ listContent(xs)
  })

  def isSorted(l: List) : Boolean = (l match {
    case Nil() => true
    case Cons(x, xs) => isSorted(xs) && (listContent(xs) == Set.empty[Int] || x <= listContent(xs).min)
  })

  def listToHeap(l: List) : Heap = {
    throw new Exception("Unimplemented")
    (DummyHeap(0) : Heap)
  } ensuring(heapContent(_) == listContent(l))

  def heapToList(h: Heap, acc: List) : List = {
    require(isSorted(acc) && (listContent(acc) == Set.empty[Int] || heapContent(h) == Set.empty[Int] || listContent(acc).min >= heapContent(h).max))
    if(isHeapEmpty(h)) {
      acc
    } else {
      heapToList(removeMax(h), Cons(findMax(h), acc))
    }
  } ensuring(res => listContent(res) == heapContent(h) ++ listContent(acc) && isSorted(res))

  // note that this does not ensure that the multiplicity of repeated elements is preserved
  def sort(l: List) : List = {
    heapToList(listToHeap(l), Nil())
  } ensuring(res => isSorted(res) && listContent(res) == listContent(l))
}
