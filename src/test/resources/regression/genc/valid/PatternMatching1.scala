/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object PatternMatching1 {

  def testLiteralSimple(x: Int) = x match {
    case 42 => 0
    case 58 => 1
    case _ => 2
  }

  def testLiteralConditional(x: Int) = x match {
    case y if y < 0 => -1
    case z if z == 0 => 0
    case a if a % 2 == 0 => 1
    case _ => 2
  }

  def power2(pow: Int): Int = {
    require(pow < 31 && pow >= 0)

    var res = 1
    var n = pow

    while (n > 0)
      res = res * 2

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

    printOnFailure(
      expect(0, testLiteralSimple(42)) +
      expect(1, testLiteralSimple(58)) +
      expect(2, testLiteralSimple(100)) +
      expect(-1, testLiteralConditional(-10)) +
      expect(0, testLiteralConditional(0)) +
      expect(1, testLiteralConditional(16)) +
      expect(2, testLiteralConditional(3))
    )
  } ensuring { _ == 0 }

  // Because on Unix, exit code should be in [0, 255], we print the exit code on failure
  // and return 1. On success, we do nothing special.
  def printOnFailure(exitCode: Int): Int = {
    if (exitCode == 0) 0
    else {
      implicit val state = leon.io.newState
      leon.io.StdOut.print("Error code: ")
      leon.io.StdOut.print(exitCode)
      leon.io.StdOut.println()
      1
    }
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}


