/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

// Unapply pattern is not supported by GenC
object Odd {
  def unapply(p: (Int, Int)): Option[Int] = {
    val x = p._1
    if (x % 2 == 1) Some(x) else None[Int]
  }
}

object InvalidPatternMatching {

  def test(x: Option[(Int, Int)]) = x match {
    case None() => 0
    case Some(Odd(y)) if y > 0 => y
    case Some(Odd(y)) if y <= 0 => -y
    case Some((a, b)) if a > b => a
    case Some((a, b)) => b
  }

  def power2(pow: Int): Int = {
    require(pow < 31 && pow >= 0)

    var res = 1
    var n = pow

    while (n > 0) {
      res = res * 2
    }

    res
  }

  def _main() = {
    var testCount = 0

    def expect(value: Int, actual: Int): Int = {
      require(testCount >= 0 && testCount < 30)

      testCount = testCount + 1

      if (value == actual) 0
      else power2(testCount)
    }

    expect(42, test(Some((42, 0)))) +
    expect(42, test(Some((0, 42)))) +
    expect(1, test(Some((-1, 99)))) +
    expect(1, test(Some((1, 99)))) +
    expect(0, test(None[(Int, Int)]))
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

