/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions3 {

  def apply(fun: Int => Int, x: Int): Int = fun(x)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    var y = 5
    def fun(x: Int) = x + y
    y = -2

    apply(fun, 2) // Not allowed: reference to a function capturing its env.
  }

}

