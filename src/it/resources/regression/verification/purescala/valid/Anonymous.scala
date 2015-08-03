/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._

object Anonymous {
  def test(x: BigInt) = {
    require(x > 0)
    val i = (a: BigInt) => a + 1
    i(x) + i(2)
  } ensuring { res => res > 0 }
}
