import leon.annotation._
import leon.lang._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def insert1(l: List, v: Int) = (
    Cons(v, l)
  ) ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def insert2(l: List, v: Int): List = (l match {
    case Nil() => Cons(v, Nil())
    case Cons(x, tail) => if (x == v) l else Cons(x, insert2(tail, v))
  }) ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def insert3(l: List, v: Int): List = {
    require(isStrictlySorted(l))

    l match {
      case Nil() => Cons(v, Nil())
      case Cons(x, tail) =>
        if (v < x) {
          Cons(v, l)
        } else if (v == x) {
          l
        } else {
          Cons(x, insert3(tail, v))
        }
    }
  } ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def delete1(l: List, v: Int): List = (l match {
      case Nil() => Nil()
      case Cons(x, tail) => if (x == v) delete1(tail, v) else Cons(x, delete1(tail, v))
    }) ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  //def delete2(l: List, v: Int): List = {
  //  require(isStrictlySorted(l))

  //  l match {
  //    case Nil() => Nil()
  //    case Cons(x, tail) =>
  //      if (x == v) {
  //        tail
  //      } else {
  //        Cons(x, delete2(tail, v))
  //      }
  //  }
  //} ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => if(elem == x) true else contains(xs, elem)
  }) ensuring(res => res == content(list).contains(elem))

  def deleteMagic(head: Int, tail: List, toDelete: Int): List = ({
    //require(isStrictlySorted(Cons(head, tail)) && toDelete < head);
    require(isStrictlySorted(Cons(toDelete, Cons(head, tail))))

    Cons(head, tail)
  })ensuring(res => !(content(res) contains toDelete))

  def delete3(l: List, v: Int): List = {
    require(isStrictlySorted(l))

    l match {
      case Nil() => Nil()
      case Cons(x, tail) =>
        if (x == v) {
          tail
        } else if (v < x) {
          deleteMagic(x, tail, v)
        } else {
          Cons(x, delete3(tail, v))
        }
    }
  } ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  @induct
  def isStrictlySorted(l: List): Boolean = (l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs @ Cons(y, ys)) => {
      if(x < y) {
        if(isStrictlySorted(xs)) discard(ltaLemma(x, y, ys)) else false
      } else {
        false
      }
    }
  }) ensuring(res => !res || (l match {
    case Nil() => true
    case Cons(x, xs) => lessThanAll(x, xs)
  }))

  def lessThanAll(x : Int, l : List) : Boolean = (l match {
    case Nil() => true
    case Cons(y, ys) => if(x < y) lessThanAll(x, ys) else false
  }) ensuring(res => !res || !contains(l, x))

  def discard(value : Boolean) = true

  @induct
  def ltaLemma(x : Int, y : Int, l : List) : Boolean = {
    require(lessThanAll(y, l) && x < y)
    lessThanAll(x, Cons(y, l))
  } holds

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
}
