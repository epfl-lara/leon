/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object BadInheritance2 {

  abstract class Base {
    def get: Int // Defining abstract method is not supported
  }

  case class Derived1(x: Int) extends Base {
    override def get: Int = 0
  }

  case class Derived2(x: Int) extends Base {
    override def get: Int = 1
  }

  def _main() = {
    0
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


