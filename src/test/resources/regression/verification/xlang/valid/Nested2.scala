/* Copyright 2009-2013 EPFL, Lausanne */

object Nested2 {

  def foo(a: Int): Int = {
    require(a >= 0)
    val b = a + 2
    def rec1(c: Int): Int = {
      require(c >= 0)
      b + c
    }
    rec1(2)
  } ensuring(_ > 0)

}
