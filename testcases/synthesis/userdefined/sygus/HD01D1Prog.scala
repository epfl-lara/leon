import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Commutative {
  
  @production(1)
  def v = variable[Int]
  
  @production(1)
  def and(x: Int, y: Int) = x & y
  
  @production(1)
  def sub(x: Int, y: Int) = x - y

  @production(1)
  def or(x: Int, y: Int) = x | y

  @production(1)
  def add(x: Int, y: Int) = x + y

  @production(1)
  def xor(x: Int, y: Int) = ~(x | y)

  
  @production(1)
  def c1 = 0

  @production(1)
  def c2 = ~0

  @production(1)
  def c3 = 1

  def hd01(x: Int) = x & (x - 1)

  def f(x: Int) = ???[Int] ensuring ( _ == hd01(x))
  
}
