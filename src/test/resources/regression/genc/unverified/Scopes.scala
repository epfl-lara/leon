/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object Scopes {

  case class W[T](x: T)

  def woo(x: Int) = W(x)
  def woo(x: Boolean) = W(x)

  abstract class Option[T]
  case class Some[T](x: T) extends Option[T]
  case class None[T]() extends Option[T]

  def opt(x: Int) = Some(x)
  def opt(x: Boolean) = Some(x)

  def scope = {
    def gen2[A, B](a: A, b: B) = 0

    def gen1[A](a: A) = gen2(a, a)

    def bar[A](a: A) = gen2(0, a)

    val v = bar(gen1(0))
  }

  def scope2 = {

    def none(x: Int) = x

    val a = 42

    def withA(x: Int) = none(x + a)

    def alsoWithA(x: Int, y: Int) = withA(x + y)

    val b = 58

    def withAandB() = none(a + b)

    def nesting() = {
      def againWithAandB() = a + b

      val c = 100

      def withMoreVars(x: Int) = a + b + c + x

      withMoreVars(-100)
    }

    val c = 31415926

    def genericId[T](x: T) = x

    val d = genericId(c)
    val e = genericId(true)

    def genericAndComplexIdFunction[T](f: T) = {
      def subsubsubsub(g: T) = g

      subsubsubsub(f)
    }

    val xxx = genericAndComplexIdFunction(false)

    nesting() // 100
  }

  def scope3[T](t: T) = {
    val x = 0

    def unused(u: T) = 0

    def inner() = x

    val y = inner()

    y
  }

  def foo(x: Int) = x

  def two[A, B](a: A, b: B) = 0
  def one[C](c: C) = two(c, 0)
  def zero() = two(0, 0)

  def oneA[A](a: A) = two(a, 0)
  def oneB[B](b: B) = two(0, b)

  def oneABbool() = oneA(true) + oneB(false)
  def oneABint() = oneA(42) + oneB(58)

  case class Pair[A, B](a: A, b: B)

  def pairII() = Pair(0, 0)
  def pairIB() = Pair(0, true)
  def pairBI() = Pair(true, 0)
  def pairBB() = Pair(true, true)

  def _main() = {
    scope
    scope2
    scope3(true)
    scope3(42)

    val x = 42
    val y = foo(x)
    val z = zero()
    val ab = oneABbool() + oneABint()

    val p1 = pairII()
    val p2 = pairIB()
    val p3 = pairBI()
    val p4 = pairBB()
    val p5 = pairBB()
    val p6 = Pair(true, true)

    val w1 = woo(42)
    val w2 = woo(false)

    val o1 = opt(42)
    val o2 = opt(false)

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

