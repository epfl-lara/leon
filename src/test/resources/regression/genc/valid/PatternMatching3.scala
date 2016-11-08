/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object PatternMatching3 {

  def testCaseClass(x: Option[Int]) = x match {
    case y @ Some(z) if z > 0 => z
    case zero: Some[Int] => 0
    case b @ _ => 999
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

    expect(42, testCaseClass(Some(42))) +
    expect(0, testCaseClass(Some(0))) +
    expect(999, testCaseClass(None[Int]))
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


