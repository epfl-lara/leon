/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object BadInheritance1 {

  abstract class Base {
    def get: Int = 1
  }

  case class Derived1(x: Int) extends Base

  case class Derived2(x: Int) extends Base {
    override def get: Int = 0 // Overriding a method is not supported
  }

  def _main() = {
    0
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


