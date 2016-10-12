/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance8 {

  abstract class Base {
    def get: Int = 1
  }

  case class Derived1(x: Int) extends Base

  case class Derived2(x: Int) extends Base {
    override def get: Int = 0 // Overriding a method IS supported
  }

  def test1 = Derived1(42).get - 1 // == 0
  def test2 = Derived2(58).get     // == 0

  def _main() = {
    test1 + test2
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


