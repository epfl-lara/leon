/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object ObjectHierarchyMutation3 {

  case class A(var x: Int)
  case class B(a: A)

  def updateB(b: B): Unit = {
    b.a.x = 42
  }

  def updateA(a: A): Unit = {
    updateB(B(a))
  } ensuring(_ => a.x == 42)

  def _main(): Int = {
    val a = A(0)
    updateA(a)

    a.x - 42 // == 0
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}
