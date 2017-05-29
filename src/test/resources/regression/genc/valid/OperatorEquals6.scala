/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals6 {

  case class T(var x: Int)

  def test(t1: T, t2: T) = t1 == t2

  def _main(): Int = {
    val x = T(42)
    val y = T(42)
    if (test(x, y)) {
      x.x = 0
      if (test(x, y)) 2
      else 0
    }
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

