/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object PatternMatching5 {

  @inline
  def foo(): (Int, Int) = {
    var index = 0
    var value: Int = Byte.MinValue

    (value, index)
  }

  def bar {
    val (a, b) = foo()
  }

  @inline
  def fun(): (Array[Int], Int) = {
    val a = Array(0, 1)
    var idx = 0
    (a, idx)
  }

  def gun {
    val (dict, index) = fun()
  }

  def simple1: Int = {
    val (one, two) = (1, 2)
    one + two
  }

  def simple2(t: (Byte, Byte)): Int = {
    val (x, y) = t
    x + y
  }

  def _main(): Int = {
    // bar & gun test compilation only, not execution
    bar
    gun

    val test1 = simple1 - 3
    val test2 = simple2((42, 58)) - 100

    test1 + test2
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

