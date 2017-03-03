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

    printOnFailure(
      expect(42, testCaseClass(Some(42))) +
      expect(0, testCaseClass(Some(0))) +
      expect(999, testCaseClass(None[Int]))
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


