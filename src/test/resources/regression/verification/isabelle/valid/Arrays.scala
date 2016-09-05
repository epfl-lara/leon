/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Arrays {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2 && a(2) == 5)
    a(2)
  } ensuring(_ == 5)

  def bar(): Int = {
    val a = Array.fill(5)(5)
    foo(a)
  }

  def bar2(): Int = {
    val a = Array(0, 1, 5, 2, 3)
    foo(a)
  }

  @isabelle.proof(method = "(unat_arith, (simp add: unat_of_nat)?)")
  def foo2(a: Array[Int]): Array[Int] = {
    require(a.length >= 2)
    a.updated(1, 3)
  } ensuring(res => res.length == a.length && res(1) == 3)

}
