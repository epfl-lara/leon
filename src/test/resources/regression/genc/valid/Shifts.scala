/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Shifts {

  // Remember from C: 1 << 31 is undefined but 1u << 31 is well defined.
  def _main(): Int = {
    val x = 0x1
    val y = 31

    val z = (x << y) >>> y

    if (z == x) 0 else 1
  }

  @extern
  def main(args: Array[String]) = _main()

}

