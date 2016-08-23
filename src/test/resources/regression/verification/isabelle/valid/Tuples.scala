/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Tuples {

  def select(x: (BigInt, BigInt, BigInt)) = {
    require(x._1 <= x._2 && x._2 <= x._3)
    (x._1 <= x._3)
  }.holds

}
