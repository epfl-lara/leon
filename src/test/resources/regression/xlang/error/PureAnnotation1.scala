/* Copyright 2009-2016 EPFL, Lausanne */
import leon.annotation._

object PureAnnotation1 {

  @pure
  def foo(a: Array[Int]): Unit = {
    a(0) = 42
  }

}

