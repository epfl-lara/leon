/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions6 {

  case class M(var x: Int)

  def square(m: M): Unit = { m.x *= m.x }

  def apply(fun: M => Unit, m: M): Unit = fun(m)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val m = M(4)

    apply(square, m)

    m.x - 16
  } ensuring { _ == 0 }

}


