/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance3 {

  abstract class Base

  abstract class Derived extends Base

  case class One(x: Int) extends Base
  case class Two(x: Int, y: Int) extends Derived
  case class Three(x: Int, y: Int, z: Int) extends Derived

  def _main() = {
    val a = One(1)
    val b = Two(2, 2)
    val c = Three(3, 3, 3)
    if (a.x + b.x + c.x == 6) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


