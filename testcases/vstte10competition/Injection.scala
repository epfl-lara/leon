import scala.collection.immutable.Set
import funcheck.Utils._
import funcheck.Annotations._

object Injection {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class OptionInt
  case class Some(value : Int) extends OptionInt
  case class None() extends OptionInt

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(list : List) : Set[Int] = list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => content(xs) ++ Set(x)
  }

  def completeSet(n : Int) : Set[Int] = if(n <= 0) {
    Set.empty[Int]
  } else {
    completeSet(n-1) ++ Set(n-1)
  }

  def at(list : List, i : Int) : OptionInt = {
    if(i < 0) None() else list match {
      case Nil() => None()
      case Cons(x, _) if i == 0 => Some(x)
      case Cons(_, xs) => at(xs, i - 1)
    }
  } ensuring(res => (res == None()) == (i < 0 || i >= size(list)))

  def reverse(l: List) : List = reverse0(l, Nil())
  def reverse0(l1: List, l2: List) : List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverse0(xs, Cons(x, l2))
  }) ensuring(res =>
    size(res) == size(l1) + size(l2) &&
    content(res) == content(l1) ++ content(l2))

  def isPermutation(list : List, n : Int) : Boolean = {
    n < 0 || (size(list) == n && content(list) == completeSet(n))
  }
  def prop0(list : List, n : Int) : Boolean = {
    require(n >= 0 && isPermutation(list, n))
    isPermutation(reverse(list), n)
  } holds

  def indexOf(e : Int, list : List) : Int = (list match {
    case Nil() => 0
    case Cons(x, xs) => if (x == e) 0 else 1 + indexOf(e, xs)
  }) ensuring(res => (res == size(list)) == !content(list).contains(e))

  // def invert(list : List, n : Int) : List = {
  //   require(isPermutation(list, n))
  //   list
  // } ensuring(res => isPermutation(res, n))

  def f(list : List) = f0(list, size(list)-1, Nil())
  def f0(list : List, c : Int, acc : List) : List = {
    require(isPermutation(list, size(list)) && c <= size(list))
    if(c < 0) {
      acc
    } else {
      f0(list, c-1, Cons(indexOf(c, list), acc))
    }
  } ensuring(res => content(acc) -- completeSet(n) == Set.empty)

  def main(args : Array[String]) : Unit = {
    val test = Cons(9, Cons(3, Cons(8, Cons(2, Cons(7, Cons(4, Cons(0, Cons(1, Cons(5, Cons(6, Nil()))))))))))
    println(f(test, size(test)))
  }
}
