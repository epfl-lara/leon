/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions1 {

  def square(x: Int): Int = x * x

  def apply(fun: Int => Int, x: Int): Int = fun(x)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val y = 5
    apply({ x: Int => square(y) }, 2) // Not allowed: capturing y
  }

}

