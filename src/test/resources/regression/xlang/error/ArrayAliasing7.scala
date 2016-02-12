/* Copyright 2009-2015 EPFL, Lausanne */

object ArrayAliasing7 {

  def foo(a: Array[Int]): Array[Int] = {
    val b = a
    b
  }

}
