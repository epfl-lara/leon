/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions1 {

  def square(x: Int): Int = x * x
  def double(x: Int): Int = x + x

  def apply(fun: Int => Int, x: Int): Int = fun(x)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val fun = double _
    apply(square, 2) - apply(fun, 2)
  } ensuring { _ == 0 }

}


