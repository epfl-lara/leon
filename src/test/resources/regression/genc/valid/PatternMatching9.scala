/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object PatternMatching9 {

  case class Wrapper(var x: Int)

  def _main(): Int = {
    var c = 1

    def get0(): Int = {
      c -= 1
      0
    }

    val array = Array(Wrapper(42))
    array(get0()) match {
      case w if w.x == 42 => w.x = 0
      case w => w.x = -1
    }

    array(0).x + c
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

