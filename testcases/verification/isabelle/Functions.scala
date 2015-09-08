import leon._
import leon.annotation._
import leon.collection._
import leon.lang._

object Functions {

  def zero: BigInt = 0

  def length[A](xs: List[A]): BigInt = {
    val ys = xs
    val zs = ys
    ys match {
      case Nil() => zero
      case Cons(_, xs) => BigInt(1) + length(xs)
    }
  } ensuring (_ >= zero)

}
