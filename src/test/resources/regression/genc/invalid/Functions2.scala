/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions2 {

  def apply(fun: Int => Int, x: Int): Int = fun(x)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    apply({ x: Int => x - x }, 2) // Not allowed: not a named function
  }

}

