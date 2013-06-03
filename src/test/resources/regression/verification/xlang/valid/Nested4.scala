/* Copyright 2009-2013 EPFL, Lausanne */

object Nested4 {

  def foo(a: Int, a2: Int): Int = {
    require(a >= 0 && a <= 50)
    val b = a + 2
    val c = a + b
    if(a2 > a) {
      def rec1(d: Int): Int = {
        require(d >= 0 && d <= 50)
        val e = d + b + c + a2
        e
      } ensuring(_ > 0)
      rec1(2)
    } else {
      5
    }
  } ensuring(_ > 0)

}
