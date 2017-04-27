/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals1 {

  case class T(x: Int)

  def _main(): Int = {
    val x = T(42)
    val y = T(42)
    if (x == y) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

