/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance5 {

  abstract class Base {
    def get: Int = this match {
      case One(x)         => x
      case Two(x, y)      => x + y
      case Three(x, y, z) => x + y + z
    }
  }

  abstract class Derived extends Base

  case class One(x: Int) extends Base
  case class Two(x: Int, y: Int) extends Derived
  case class Three(x: Int, y: Int, z: Int) extends Derived

  def foo(b: Base) = b

  def test0(): Boolean = { One(0).get == 0              }.holds
  def test1(): Boolean = { foo(One(42)).get == 42       }.holds
  def test2(): Boolean = { foo(Two(42, 58)).get == 100  }.holds
  def test3(): Boolean = { foo(Three(1, 2, 3)).get == 6 }.holds

  def _main() = {
    bool2int(test0(), 1)  +
    bool2int(test1(), 2)  +
    bool2int(test2(), 4)  +
    bool2int(test3(), 8)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

  def bool2int(b: Boolean, f: Int) = if (b) 0 else f

}


