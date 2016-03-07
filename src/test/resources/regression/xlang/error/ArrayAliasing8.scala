/* Copyright 2009-2016 EPFL, Lausanne */

object ArrayAliasing8 {

  def foo(a: Array[Int]): Int = {
    def rec(): Array[Int] = {
      a
    }
    val b = rec()
    b(0)
  }

}
