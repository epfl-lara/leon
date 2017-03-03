/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance1 {

  abstract class Base
  case class Derived1(x: Int) extends Base
  case class Derived2(x: Int, y: Int) extends Base

  def _main() = {
    val d1 = Derived1(0)
    val d2 = Derived2(1, 2)
    if (d1.x + d2.x + d2.y == 3) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


