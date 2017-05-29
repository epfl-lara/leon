/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions3 {

  def square(x: Int): Int = x * x

  def id(f: Int => Int): Int => Int = f

  def apply(fun: Int => Int, x: Int): Int = fun(x)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    apply(id(square), 0)
  } ensuring { _ == 0 }

}


