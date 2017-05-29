/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals8 {

  case class T(var x: Int)

  def test(t2: T) = {
    val t1 = T(0)
    t1 == t2
  }

  def _main(): Int = {
    val t2 = T(0)
    if (test(t2)) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

