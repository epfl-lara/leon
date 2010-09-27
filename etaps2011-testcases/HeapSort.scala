import scala.collection.immutable.Set

object HeapSort {
  sealed abstract class Heap
  case class DummyHeap(i: Int) extends Heap

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

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
  } ensuring(heapContent(_) == heapContent(h) -- Set(heapContent(h).max))

  def listContent(l: List) : Set[Int] = (l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ listContent(xs)
  })

  def isSorted(l: List) : Boolean = (l match {
    case Nil() => true
    case Cons(x, xs) => isSorted(xs) && (listContent(xs) == Set.empty[Int] || x < listContent(xs).min)
  })

  def listToHeap(l: List) : Heap = {
    throw new Exception("Unimplemented")
    (DummyHeap(0) : Heap)
  } ensuring(heapContent(_) == listContent(l))

  def heapToList(h: Heap, acc: List) : List = {
    require(isSorted(acc) && (listContent(acc) == Set.empty[Int] || heapContent(h) == Set.empty[Int] || listContent(acc).min > heapContent(h).max))
    if(isHeapEmpty(h)) {
      acc
    } else {
      heapToList(removeMax(h), Cons(findMax(h), acc))
    }
  } ensuring(res => listContent(res) == heapContent(h) ++ listContent(acc) && isSorted(res))

  def sort(l: List) : List = {
    heapToList(listToHeap(l), Nil())
  } ensuring(listContent(_) == listContent(l))
}
