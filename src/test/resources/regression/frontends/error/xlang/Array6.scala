/* Copyright 2009-2014 EPFL, Lausanne */


object Array6 {

  def foo(): Int = {
    val a = Array.fill(5)(5)
    var b = a
    b(0)
  }

}
