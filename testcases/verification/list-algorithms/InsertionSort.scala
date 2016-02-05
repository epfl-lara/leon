import leon.annotation._
import leon.lang._

object InsertionSort {
  sealed abstract class List
  case class Cons(head: BigInt,tail: List) extends List
  case class Nil() extends List

  sealed abstract class OptInt
  case class Some(value: BigInt) extends OptInt
  case class None() extends OptInt

  def size(l : List) : BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contents(l: List): Set[BigInt] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def min(l : List) : OptInt = l match {
    case Nil() => None()
    case Cons(x, xs) => min(xs) match {
      case None() => Some(x)
      case Some(x2) => if(x < x2) Some(x) else Some(x2)
    }
  }

  def minProp0(l : List) : Boolean = (l match {
    case Nil() => true
    case c @ Cons(x, xs) => min(c) match {
      case None() => false
      case Some(m) => x >= m
    }
  }) holds

  def minProp1(l : List) : Boolean = {
    require(isSorted(l) && size(l) <= 5)
    l match {
      case Nil() => true
      case c @ Cons(x, xs) => min(c) match {
        case None() => false
        case Some(m) => x == m
      }
    }
  } holds

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def sortedIns(e: BigInt, l: List): List = {
    require(isSorted(l))
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => contents(res) == contents(l) ++ Set(e)
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def buggySortedIns(e: BigInt, l: List): List = {
    // require(isSorted(l))
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,buggySortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => contents(res) == contents(l) ++ Set(e)
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* Insertion sort yields a sorted list of same size and content as the input
   * list */
  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => contents(res) == contents(l)
                     && isSorted(res)
                     && size(res) == size(l)
             )

  @ignore
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(sort(ls))
  }
}
