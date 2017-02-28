/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object ArrayCopy {

  def _main(): Int = {
    val a = Array(0, 5, 3, 10, -5)
    val b = a.updated(0, 1)
    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}
