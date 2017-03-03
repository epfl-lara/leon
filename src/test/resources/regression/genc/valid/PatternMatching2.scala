/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object PatternMatching2 {

  def testScrutineeSideEffect(x: Int) = {
    var local = 0

    def inc() { local = local + 1 }

    // NOTE: using inc() or modifying local in foo or bar results in
    // java.util.NoSuchElementException: key not found: def foo$0(a$4 : Int): Boolean = inc$0
    // or similar when verifying this file (due to the call being in the pattern matching guard statements)
    // In any case, we DON'T want that!
    def foo(a: Int): Boolean = { 42 == a }
    def bar(a: Int): Boolean = { local == a }

    { inc(); x } match {
      case y if foo(y) => local
      case y if bar(1) => 0
      case _ => -1
    }
  } ensuring { res => res != -1 }

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
      expect(0, testScrutineeSideEffect(999)) +
      expect(1, testScrutineeSideEffect(42)) +
      expect(0, testScrutineeSideEffect(0))
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


