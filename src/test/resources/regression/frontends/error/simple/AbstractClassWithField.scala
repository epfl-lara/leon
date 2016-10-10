/* Copyright 2009-2016 EPFL, Lausanne */

object AbstractClassWithField {
  abstract class Base(x: Int)
  case class Derived() extends Base(42)
}

