/* Copyright 2009-2014 EPFL, Lausanne */

object Array1 {

  def foo(): Int = {
    (Array.fill(5)(5))(2) = 3
    0
  }

}
