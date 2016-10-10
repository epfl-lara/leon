/* Copyright 2009-2016 EPFL, Lausanne */

object AbstractClassWithVar {
  abstract class Base() {
    var x = 0
  }
  case class Derived() extends Base()
}

