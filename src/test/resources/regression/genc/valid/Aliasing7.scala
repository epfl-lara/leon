/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Aliasing7 {

  case class Mutable(var i: Int)

  case class Wutable(var x: Int, val m: Mutable)

  def inc(x: Int): Int = {
    require(x < 1000)
    x + 1
  }

  def foo(x: Int, m: Mutable): Int = {
    m.i += 1
    x + m.i
  }

  def _main(): Int = {
    val w = Wutable(42, Mutable(58))

    val s = foo(inc(w.x), w.m)

    if (s == 102) {
      if (w.m.i == 59) 0
      else 1
    } else 2
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

