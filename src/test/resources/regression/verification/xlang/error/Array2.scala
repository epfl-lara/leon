/* Copyright 2009-2013 EPFL, Lausanne */

object Array2 {

  def foo(): Int = {
    val a = Array.fill(5)(5)
    val b = a
    b(3)
  }

}
