/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._

object Array6 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2 && a(2) == 5)
    a(2)
  } ensuring(_ == 5)

  def bar(): Int = {
    val a = Array.fill(5)(5)
    foo(a)
  }

}
