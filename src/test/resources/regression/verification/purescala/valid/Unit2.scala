/* Copyright 2009-2013 EPFL, Lausanne */

object Unit2 {

  def foo(u: Unit): Unit = {
    u
  } ensuring(res => true)

}
