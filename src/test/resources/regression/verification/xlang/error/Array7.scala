/* Copyright 2009-2013 EPFL, Lausanne */

object Array7 {

  def foo(): Int = {
    val a = Array.fill(5)(5)
    var b = a
    b(0)
  }

}
