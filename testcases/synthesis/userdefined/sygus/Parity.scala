import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Commutative {
  
  @production(4)
  def v = variable[Boolean]
  
  @production(1)
  @tag("not")
  def not(x: Boolean) = !x
  
  @production(1)
  @tag("and")
  def and(x: Boolean, y: Boolean) = x && y

  // @inline def xor(a: Boolean, b: Boolean) = a != b

  def parity(a: Boolean, b: Boolean, c: Boolean, d: Boolean): Boolean = (
    (a == b) != (c == d)
  )


  def AIG(a: Boolean, b: Boolean, c: Boolean, d: Boolean): Boolean = ???[Boolean] ensuring ( _ == parity(a, b, c,d))
}
