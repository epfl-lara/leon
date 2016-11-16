/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals {

  case class T(x: Int)

  def _main(): Int = {
    val x = T(42)
    val y = T(42)
    // Custom operator `==` not supported
    if (x == y) 0
    else 1
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

