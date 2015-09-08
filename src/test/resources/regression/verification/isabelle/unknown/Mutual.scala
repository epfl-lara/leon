import leon.annotation._
import leon.lang._

object Mutual {

  sealed abstract class List1[A]
  case class Cons1[A](head: A, tail: List2[A]) extends List1[A]

  sealed abstract class List2[B]
  case class Cons2[B](head: B, tail: List1[B]) extends List2[B]
  case class Nil2[B]() extends List2[B]

  def size1[A](list: List1[A]): BigInt = (list match {
    case Cons1(_, t) => 1 + size2(t)
  }) ensuring { _ >= BigInt(0) }

  def size2[A](list: List2[A]): BigInt = (list match {
    case Nil2() => BigInt(0)
    case Cons2(_, t) => 1 + size1(t)
  }) ensuring { _ >= BigInt(0) }

}
