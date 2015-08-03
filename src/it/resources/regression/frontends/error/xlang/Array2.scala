/* Copyright 2009-2015 EPFL, Lausanne */

object Array2 {

  def foo(): Int = {
    val a = Array.fill(5)(5)
    val b = a
    b(3)
  }

}
