/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions5 {

  case class FunWrapper(fun: Int => Int) {
    def run(x: Int): Int = id(fun)(x)
  }

  def id(f: Int => Int) = f

  def square(x: Int): Int = x * x

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val w = FunWrapper(square)
    val v = FunWrapper(id(w.fun))
    v.run(4) - 16
  } ensuring { _ == 0 }

}


