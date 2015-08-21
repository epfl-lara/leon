/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._

object Array6 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(1, 2)
    a2(0)
  }

}
