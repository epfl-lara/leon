/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Aliasing2 {

  case class MutableInteger(var x: Int)

  def validator(v: MutableInteger) = {
    if (v.x == 42) MutableInteger(58)
    else {
      v.x = 0
      MutableInteger(0)
    }
  }

  def testTemporary(): Int = {
    validator(MutableInteger(42)).x
  } ensuring { _ == 58 }

  def _main(): Int = {
    if (testTemporary() == 58) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

