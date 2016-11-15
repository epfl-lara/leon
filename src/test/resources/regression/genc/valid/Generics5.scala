/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Generics5 {
  case class Dummy[T](t: T)

  def fun[T](x: Int) = x

  def gun[T](x: T) = x

  def _main() = {
    fun[Int](58) - 58 /* == 0 */ + gun(42) - 42 /* == 0 */ + fun[Char](0)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

