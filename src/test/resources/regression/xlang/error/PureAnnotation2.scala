/* Copyright 2009-2016 EPFL, Lausanne */
import leon.annotation._

object PureAnnotation2 {

  case class A(var x: Int)

  @pure
  def foo(a: A): Int  = {
    a.x = a.x + 1
    a.x
  }

}

