package test.resources.regression.xlang.error

import leon.lang._

object ObjectAliasing7 {

  case class A(var x: Int)
  case class B(a: A)

  def f1(a1: A, a2: A): Int = {
    val tmp = a1.x
    a2.x = a1.x
    a1.x = tmp
    a1.x + a2.x
  }

  def f(): Int = {
    val b = B(A(10))
    f1(b.a, b.a)
  } ensuring(_ == 20)

}
