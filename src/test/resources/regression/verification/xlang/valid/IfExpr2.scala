/* Copyright 2009-2016 EPFL, Lausanne */
import leon.annotation._

object IfExpr2 {

  @pure
  def foo(): Int = {
    var a = 1
    var b = 2
    if(a < b) {
      a = a + 3
      b = b + 2
      a = a + b
    }
    a
  } ensuring(_ == 8)

}
