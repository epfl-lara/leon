/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Asserts2 {

  def assert1(i: BigInt): BigInt = { // we might define assert like so
    require(i >= 0)
    i
  }

  def sum(to: BigInt): BigInt = {
    assert1(to)
    to
  }
}
