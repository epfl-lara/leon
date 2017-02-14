/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object PatternMatching6 {

  case class Pair(x: Int, y: Int)

  def max(p: Pair): Int = {
    val Pair(x, y) = p
    if (x >= y) x else y
  }

  def min(p: Pair): Int = {
    val Pair(x, y) = p
    if (x <= y) x else y
  }

  def sum(p: Pair): Int = {
    min(p) + max(p)
  }

  def _main(): Int = {
    val p = Pair(-1, 1)
    sum(p)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

