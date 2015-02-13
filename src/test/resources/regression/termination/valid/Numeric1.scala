/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Numeric {

  def f1(x: BigInt): BigInt = f2(x - 2)

  def f2(x: BigInt): BigInt = if (x < 0) 0 else f1(x + 1)
}
