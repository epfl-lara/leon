/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals4 {

  abstract class Top
  case class ChildA(x: Int) extends Top
  case class ChildB(y: Boolean) extends Top

  def foo = ChildA(42)
  def bar = ChildB(true)

  def factory(zero: Int): Top = if (zero == 0) foo else bar

  def _main(): Int = {
    val a = factory(0)
    val b = factory(1)

    if (a == b) {
      if (a != b) 2
      else 1
    } else 0

  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

