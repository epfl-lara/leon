/* Copyright 2009-2014 EPFL, Lausanne */

object Array10 {

  def foo(): Int = {
    val a = Array.fill(5)(0)
    def rec(): Array[Int] = {
      a
    }
    val b = rec()
    b(0)
  }

}
