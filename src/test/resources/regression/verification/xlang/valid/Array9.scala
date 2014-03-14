/* Copyright 2009-2014 EPFL, Lausanne */

object Array9 {

  def foo(i: Int): Array[Int] = {
    require(i > 0)
    val a = Array.fill(i)(0)
    a
  } ensuring(res => res.length == i)

  def bar(i: Int): Int = {
    require(i > 0)
    val b = foo(i)
    b(0)
  }

}
