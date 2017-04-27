/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals2 {

  case class T(var x: Int)

  def _main(): Int = {
    val x = T(42)
    val y = T(42)
    if (x == y) {
      x.x = 0
      if (x == y) 2
      else 0
    }
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

