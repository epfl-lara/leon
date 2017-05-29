/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object PatternMatching7 {

  case class Wrapper(var x: Int)

  def _main(): Int = {
    val array = Array(Wrapper(42))
    array(0) match {
      case w => w.x = 0
    }
    array(0).x
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

