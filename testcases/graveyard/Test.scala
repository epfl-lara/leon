import leon.lang._
import leon.annotation._

object Test {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    @axiomatize
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    // @axiomatize
    // def isSorted(l : List) : Boolean = l match {
    //   case Nil() => true
    //   case Cons(x, xs) => xs match {
    //     case Nil() => true
    //     case Cons(y, _) => x <= y && isSorted(xs)
    //   }
    // }

    @axiomatize
    def content(l : List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }
  

    // def valuesWithin(l: List, lower: Int, upper: Int) : Boolean = l match {
    //   case Nil() => true
    //   case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
    // }

    def findOne(l1 : List, l2 : List) : Boolean = {
      size(l1) == 2 &&
      l2 != Nil() &&
      content(l1) == content(l2)
    } //ensuring(res => !res)

    def sets(s1 : Set[Int], s2 : Set[Int], s3 : Set[Int]) : Boolean = {
      s1 != Set.empty[Int] && s2 != Set.empty[Int] &&
      s1 ++ s2 == s3
    } ensuring(res => !res)

}
