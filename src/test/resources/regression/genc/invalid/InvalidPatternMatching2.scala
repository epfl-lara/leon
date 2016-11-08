/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

case class Pair2(var x: Int, var y: Int)

object Odd2 {
  def unapply(p: Pair2): Option[Int] = {
    p.y = p.y + 1 // WITHOUT THIS IT DOESN'T CRASH
    val x = p.x
    if (x == 1) Some(x) else None[Int]
  }
}

object InvalidPatternMatching2 {

  def test2(p: Pair2) = {
    require(p.y == 0)
    p match {
      case Odd2(x) => p.y
      case _ => 0
    }
  } ensuring { res => res == p.y && p.y == 1 }

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

    expect(1, test2(Pair2(1, 0))) +
    expect(0, test2(Pair2(0, 0)))
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


