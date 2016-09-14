/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object RecursionAndNestedFunctions {

  // Complex way to return i
  def zzz(i: Int): Int = {
    val x = 0

    def rec(j: Int): Int = {
      if (i - x == j) i
      else if (j > i) rec(j - 1)
      else            rec(j + 1)
    } ensuring { _ == i }

    rec(4)
  } ensuring { _ == i }


  // Complex way to compute 100 + 2 * i
  def foo(i: Int) = {
    var j = i
    def bar(x: Int) = {
      //j = j - 1 <- not supported by leon
      val y = x + i
      def baz(z: Int) = z + y + i
      //j = j + 1 <- not supported by leon
      baz(42)
    }
    bar(58) + j - i
  } ensuring { _ == 100 + 2 * i }

  def _main() = {
    foo(2) - zzz(104)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

