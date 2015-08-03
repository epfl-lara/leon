/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.annotation._
import leon._

object Asserts1 {

  def foo(a: BigInt): BigInt = {
    require(a > 0)
    val b = a
    assert(b > 0, "Hey now")
    b + bar(1)
  } ensuring { res =>
    res > a && res < 2
  }

  def bar(a: BigInt): BigInt = {
    require(a > 0)
    val b = a
    assert(b > 0, "Hey now")
    b + 2
  } ensuring { res =>
    res > a && res > 2
  }
}
