/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Generics1 {
  case class Dummy[T](x: Int)

  def _main() = {
    val d1 = Dummy[Int](42)
    val d2 = Dummy[Char](58)

    if (d1.x + d2.x == 100) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

