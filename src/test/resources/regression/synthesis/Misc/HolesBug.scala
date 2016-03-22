/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object HolesBug {
  def plop(a: BigInt, b: BigInt): BigInt = {
    if (a < b) {
      ???[BigInt]
    } else {
      ???[BigInt]
    }
  } ensuring { res =>
    res > 0
  }
}

