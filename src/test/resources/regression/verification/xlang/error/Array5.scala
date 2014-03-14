/* Copyright 2009-2014 EPFL, Lausanne */

object Array5 {

  def foo(a: Array[Int]): Int = {
    a(2) = 4
    a(2)
  }

}

// vim: set ts=4 sw=4 et:
