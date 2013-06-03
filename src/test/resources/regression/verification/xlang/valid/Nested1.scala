/* Copyright 2009-2013 EPFL, Lausanne */

object Nested1 {

  def foo(i: Int): Int = {
    val n = 2
    def rec1(j: Int) = i + j + n
    def rec2(j: Int) = {
      def rec3(k: Int) = k + j + i
      rec3(5)
    }
    rec2(2)
  } ensuring(i + 7 == _)

}

// vim: set ts=4 sw=4 et:
