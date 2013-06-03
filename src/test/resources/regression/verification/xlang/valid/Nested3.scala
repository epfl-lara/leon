/* Copyright 2009-2013 EPFL, Lausanne */

object Nested3 {

  def foo(a: Int): Int = {
    require(a >= 0 && a <= 50)
    val b = a + 2
    val c = a + b
    def rec1(d: Int): Int = {
      require(d >= 0 && d <= 50)
      val e = d + b + c
      e
    }
    rec1(2)
  } ensuring(_ > 0)

}
