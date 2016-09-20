/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Inheritance4 {

  abstract class Base {
    def get: Int = this match {
      case Odd(x)  => x
      case Even(x) => x + 1
    }
  }

  case class Odd(x: Int) extends Base
  case class Even(x: Int) extends Base

  def foo(x: Int): Base = {
    if (x % 2 == 0) Even(x)
    else            Odd(x)
  }

  def test0(): Boolean = foo(0).get == 1
  def test1(): Boolean = foo(1).get == 1

  def _main() = {
    bool2int(test0(), 1) +
    bool2int(test1(), 2)
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

  def bool2int(b: Boolean, f: Int) = if (b) 0 else f

}


