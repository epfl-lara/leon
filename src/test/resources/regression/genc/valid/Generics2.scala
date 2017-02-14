/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Generics2 {
  case class Dummy[T](t: T)

  def _main() = {
    val d1 = Dummy(true)
    val d2 = Dummy[Int](42)

    if (d1.t && d2.t == 42) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

