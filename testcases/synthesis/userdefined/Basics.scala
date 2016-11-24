import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._
import leon.grammar._

import Basics._


object Basics {

  case class MyCC(a: BigInt, b: Boolean)

  @production
  def constructors[A]: A = constructor[A]

  @production
  def selectors[A,B](a: B): A = selector[B, A](a)

  @production
  def variableBool: Boolean = variable[Boolean]

  @production
  def zero: BigInt = 0

  @production
  def producecc(b: Boolean) = {
    MyCC(42, !b)
  }

}

object Test {

  def eq[T](a: T, b: T) = a == b

  // The only candidate should be MyCC(zero, a)
  def test1(a: Boolean, b: BigInt): MyCC = {
    ???[MyCC]
  } ensuring { r =>
    eq(r, MyCC(zero, a))
  }

  // The only candidate should be producecc(b).b
  def test2(b: Boolean): Boolean = {
    ???[Boolean]
  } ensuring { r =>
    eq(r, !b)
  }
}
