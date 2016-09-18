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
    0
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}


