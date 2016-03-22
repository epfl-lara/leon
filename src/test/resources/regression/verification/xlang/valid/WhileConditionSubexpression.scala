/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

import leon.lang._

object WhileConditionSubexpression {

  def test(x: Int): Boolean = {
    var b = false
    var i = 0
    while(!b && i < 10) {
      if(i == x)
        b = true
      i += 1
    }
    b
  } ensuring(res => res || (x != 0 && x != 1 && x != 2))

}
