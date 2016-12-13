/* Copyright 2009-2016 EPFL, Lausanne */

object Bytes2 {

  def foo(a: Array[Byte]) {
    require(a.length == 2)
    // Nothing
  }

  def bar {
    val a = Array[Byte](1, 2, 3, 4)
    foo(a)
  }

}

