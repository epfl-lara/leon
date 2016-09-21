/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance7 {

  abstract class Base {
    def get: Int // Defining abstract method IS supported
  }

  case class Derived1(x: Int) extends Base {
    override def get: Int = 0
  }

  case class Derived2(x: Int) extends Base {
    override def get: Int = 1
  }

  def test1 = Derived1(42).get     // == 0
  def test2 = Derived2(58).get - 1 // == 0

  def _main() = {
    test1 + test2
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


