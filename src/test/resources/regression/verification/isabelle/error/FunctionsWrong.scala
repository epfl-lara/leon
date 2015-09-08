import leon._
import leon.annotation._
import leon.collection._
import leon.lang._

object FunctionsWrong {

  def zero: BigInt = 0

  // unsupported by Isabelle
  // should report a 'fatal error' (not an 'internal error')

  def length[A]: List[A] => BigInt = {
    case Nil() => zero
    case Cons(_, xs) => BigInt(1) + length(xs)
  }

  def test[A](xs: List[A]) = (length(xs) >= zero) holds

}
