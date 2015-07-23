import leon.lang._
import leon.annotation._

object InsertionSort {
  sealed abstract class List
  case class Cons(head:BigInt,tail:List) extends List
  case object Nil extends List

  sealed abstract class OptInt
  case class Some(value: BigInt) extends OptInt
  case object None extends OptInt

  def size(l : List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contents(l: List): Set[BigInt] = l match {
    case Nil => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil => true
    case Cons(x, Nil) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }   

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def sortedIns(e: BigInt, l: List): List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(e,Nil)
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    } 
  } ensuring(res => contents(res) == contents(l) ++ Set(e) 
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* A counterexample is found when we forget to specify the precondition */
  def buggySortedIns(e: BigInt, l: List): List = {
    l match {
      case Nil => Cons(e,Nil)
      case Cons(x,xs) => if (x <= e) Cons(x,buggySortedIns(e, xs)) else Cons(e, l)
    } 
  } ensuring(res => contents(res) == contents(l) ++ Set(e) 
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* Insertion sort yields a sorted list of same size and content as the input
   * list */
  def sort(l: List): List = (l match {
    case Nil => Nil
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => contents(res) == contents(l) 
                     && isSorted(res)
                     && size(res) == size(l)
             )

  /* Merges one (unsorted) list into another, sorted, list. */
  def mergeInto(l1 : List, l2 : List) : List = {
    require(isSorted(l2))
    l1 match {
      case Nil => l2
      case Cons(x, xs) => mergeInto(xs, sortedIns(x, l2))
    }
  } ensuring(res => contents(res) == contents(l1) ++ contents(l2) && isSorted(res))

  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil))))))

    println(ls)
    println(sort(ls))
  }
}
