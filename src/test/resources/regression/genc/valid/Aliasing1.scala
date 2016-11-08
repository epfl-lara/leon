/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Aliasing1 {

  // Global variable are not allowed
  // var g = 0

  // This is illegal:
  // def id(m: MutableInteger) = m

  case class MutableInteger(var x: Int)

  def editor(v: MutableInteger): Unit = {
    v.x = 58
  }

  def foo(): Int = {
    val mi = MutableInteger(42)
    editor(mi)
    mi.x
  } ensuring { _ == 58 }

  def producer(x: Int) = MutableInteger(x + 10)

  def validator(v: MutableInteger) = {
    if (v.x == 42) MutableInteger(58)
    else {
      v.x = 0
      MutableInteger(0)
    }
  }

  def bar(): Int = {
    var mi1 = producer(32)
    var mi2 = validator(mi1)
    mi1.x + mi2.x
  } ensuring { _ == 100 }

  def _main(): Int = {
    if (foo() == 58 && bar() == 100) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

