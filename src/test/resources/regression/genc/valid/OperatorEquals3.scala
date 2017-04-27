/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals3 {

  case class A(b: B)
  case class B(t1: T, t2: T)
  case class T(var x: Int)

  def foo = A(B(T(0), T(1)))
  def bar = A(B(T(1), T(0)))

  def _main(): Int = {
    val a1 = foo
    val a2 = foo
    val b1 = bar

    if (a1 == foo && a2 == a1) {
      if (b1 == bar) {
        if (b1 == a1) 3
        else if (b1 != a1) 0
        else 4
      } else 2
    } else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

