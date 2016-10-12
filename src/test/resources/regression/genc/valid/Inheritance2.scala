/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance2 {

  case class Derived1(x: Int) extends Base
  case class Derived2(x: Int, y: Int) extends Base
  abstract class Base

  def _main() = {
    0
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


