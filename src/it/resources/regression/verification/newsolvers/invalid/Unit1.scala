/* Copyright 2009-2015 EPFL, Lausanne */

object Unit1 {

  def foo(u: Unit): Unit = ({
    u
  }) ensuring(res => false)

}
