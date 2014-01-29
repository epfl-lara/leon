/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Array4 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(1, 2)
    a2(0)
  }

}
