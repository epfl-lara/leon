/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object ObjectHierarchyMutation1 {

  case class A(var x: Int)
  case class B(a1: A, a2: A)

  def updateB(b: B): Unit = {
    b.a1.x = 42
    b.a2.x = 41
  }

  def updateA(a1: A, a2: A): Unit = {
    updateB(B(a1, a2))
  } ensuring(_ => a1.x == 42 && a2.x == 41)

  def _main(): Int = {
    val a1 = A(0)
    val a2 = A(0)
    updateA(a1, a2)

    a1.x - a2.x - 1 // == 0
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}
