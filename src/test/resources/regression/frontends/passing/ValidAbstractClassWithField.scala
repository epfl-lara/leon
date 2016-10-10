/* Copyright 2009-2016 EPFL, Lausanne */

object ValidAbstractClassWithField {
  abstract class Base() {
    val x = 42
  }
  case class Derived() extends Base
}

