/* Copyright 2009-2014 EPFL, Lausanne */

object Array9 {

  def foo(a: Array[Int]): Int = {
    def rec(): Array[Int] = {
      a
    }
    val b = rec()
    b(0)
  }

}
