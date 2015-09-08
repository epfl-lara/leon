import leon.annotation._
import leon.lang._

object MutualWrong {

  // unsupported by Isabelle
  // should report a 'fatal error' (not an 'internal error')

  sealed abstract class List1[A]
  case class Cons1[A](head: A, tail: List2[A, A]) extends List1[A]

  sealed abstract class List2[A, B]
  case class Cons2[A, B](head: A, tail: List1[B]) extends List2[A, B]
  case class Nil2[A, B]() extends List2[A, B]

  def truth = true holds

}
