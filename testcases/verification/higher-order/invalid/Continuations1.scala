import leon.lang._
import leon.collection._

object Continuations1 {
  def add_cps[T](x: BigInt, y: BigInt)(f: BigInt => T): T = {
    f(x + y)
  }

  def square_cps[T](x: BigInt)(f: BigInt => T): T = {
    f(x * x)
  }

  def pythagoras_cps[T](a: BigInt, b: BigInt)(f: BigInt => T): T = {
    val a2 = square_cps(a)(x => x)
    val b2 = square_cps(b)(x => x)
    add_cps(a2, b2)(f)
  }

  def lemma1(a: BigInt, b: BigInt): Boolean = {
    require(a > 0 && b > 0)
    pythagoras_cps(a, b)(_ == a*a + b*b)
  }.holds

  def lemma2(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(a > 0 && b > 0 && c > 0)
    pythagoras_cps(a, b)(_ == c*c)
  }.holds
}
