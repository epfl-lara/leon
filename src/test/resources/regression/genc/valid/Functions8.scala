/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Functions8 {

  case class M(var x: Int)

  def mutatecopy(m: M) = {
    val copy = M(m.x)
    m.x += 1
    copy
  }

  def apply(fun: M => M, m: M): M = fun(m)

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val m1 = M(1)
    val m2 = apply(mutatecopy, m1)

    m1.x - m2.x - 1
  } ensuring { _ == 0 }

}


