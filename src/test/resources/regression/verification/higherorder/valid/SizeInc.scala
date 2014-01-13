import leon.Utils._

object SizeInc {
  
  abstract class List[A]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[A]() extends List[A]

  def sizeInc[A](x: List[A]): Int => Int = {
    (i: Int) => x match {
      case Cons(head, tail) => 1 + sizeInc(tail)(i)
      case Nil() => i
    }
  } ensuring { res => forall((a: Int) => a > 0 ==> res(a) > 0) }

  def sizeInc2[A](x: Int): List[A] => Int = {
    require(x > 0)

    (list: List[A]) => list match {
      case Cons(head, tail) => 1 + sizeInc2(x)(tail)
      case Nil() => x
    }
  } ensuring { res => forall((a: List[A]) => res(a) > 0) }
}

// vim: set ts=4 sw=4 et:
