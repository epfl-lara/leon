/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Aliasing3 {

  case class MutableInteger(var x: Int)

  def scope = {
    var x = 0

    def hoo(m: MutableInteger) {
      toto()
      foo(42, m)
    }

    def foo(y: Int, m: MutableInteger) {
      toto()
      x = 1
      bar(m)
      m.x = y
    }

    foo(42, MutableInteger(58))

    val m = MutableInteger(58)

    hoo(m)

    def goo(y: Int) {
      foo(y, m)
    }
    goo(42)

    m.x
  } ensuring { _ == 42 }

  def bar(m: MutableInteger) {
    m.x = 0
  }

  def toto() = { }

  def _main(): Int = {
    if (scope == 42) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

