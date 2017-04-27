/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions7 {

  def index(xs: Array[Int]): Unit = {
    var i = 0
    (while (i < xs.length) {
      xs(i) = i + 1
      i += 1
    }) invariant (0 <= i && i <= xs.length)
  }

  def apply(fun: Array[Int] => Unit, xs: Array[Int]): Unit = fun(xs)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val xs = Array(-1, -1, -1)

    apply(index, xs)

    xs(2) - xs(1) - xs(0)
  } ensuring { _ == 0 }

}


