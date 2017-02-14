/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object ReturnArray {

  def foo: Array[Int] = Array(0, 1, 2)

  def _main(): Int = {
    val a = foo
    0
  }

  @extern
  def main(args: Array[String]) : Unit = _main()

}

