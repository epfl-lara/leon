import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object HD {
  
  @production(2)
  def v = variable[Int]
  
  @production(1)
  @tag("and")
  def and(x: Int, y: Int) = x & y
  
  @production(1)
  @tag("minus")
  def sub(x: Int, y: Int) = x - y

  @production(1)
  @tag("or")
  def or(x: Int, y: Int) = x | y

  @production(1)
  @tag("plus")
  def add(x: Int, y: Int) = x + y

  @production(1)
  def xor(x: Int, y: Int) = ~(x | y)

  @production(1)
  def lshr(x: Int, y: Int) = x >>> y

  @production(1)
  def ashr(x: Int, y: Int) = x >> y

  @production(1)
  @tag("not")
  def not(x: Int) = ~x

  @production(1)
  @tag("not")
  def neg(x: Int) = -x

  
  @production(1)
  @tag("const")
  def c1 = 0

  @production(1)
  @tag("const")
  def c2 = ~0

  @production(1)
  @tag("const")
  def c3 = 1

  def hd15(x: Int, y: Int) = (x | y) - ((x | y) >>> 1)

  def f(x: Int, y: Int) = ???[Int] ensuring ( _ == hd15(x, y))
  
}
