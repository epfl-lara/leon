/* Copyright 2009-2015 EPFL, Lausanne */

object Nested14 {

  def foo(i: Int): Int = {
    def rec1(j: Int): Int = {
      def rec2(k: Int): Int = if(k == 0) 0 else rec1(j-1)
      rec2(j)
    }
    rec1(3)
  } ensuring(0 == _)

}
