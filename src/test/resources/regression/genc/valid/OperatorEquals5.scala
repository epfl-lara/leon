/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals5 {

  abstract class Top
  case class ChildA(var x: Int) extends Top
  case class ChildB(y: Boolean) extends Top

  def foo(x: Int) = ChildA(x)
  def bar = ChildB(true)

  def factory(zero: Int): Top = if (zero == 0) bar else foo(zero)

  def _main(): Int = {
    val a = factory(0)
    val b = factory(1)
    val c = factory(2)

    if (a == b || a == c) 1
    else if (!(a != b && a != c)) 2
    else if (b == c) 3
    else {
      b.asInstanceOf[ChildA].x = 2
      if (b == c && !(b != c)) 0
      else 4
    }

  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

