/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance6 {

  abstract class Base
  case class Derived1(x: Int) extends Base
  case class Derived2(x: Int, y: Int) extends Base

  // Test instantiation of abstract type
  def foo = {
    Derived1(42)
  }

  def bar = {
    Derived2(42, 58)
  }

  def baz(unused: Base) = 0

  def _main() = {
    baz(foo) + baz(bar)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


