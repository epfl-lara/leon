/* Copyright 2009-2013 EPFL, Lausanne */

object Array10 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 0)
    val b = a.clone
    b(0)
  } ensuring(res => res == a(0))

}
