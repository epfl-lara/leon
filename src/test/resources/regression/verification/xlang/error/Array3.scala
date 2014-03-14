/* Copyright 2009-2014 EPFL, Lausanne */

object Array3 {

  def foo(): Int = {
    val a = Array.fill(5)(5)
    if(a.length > 2)
      a(1) = 2
    else 
      0
    0
  }

}
