/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object AsInstanceOf {

  abstract class Top
  abstract class Middle extends Top
  case class Bottom(x: Int) extends Middle

  // Middle is abstract and has a parent, and therefore shouldn't be used for casting
  // because we don't support it yet.
  def bad(x: Bottom) = x.asInstanceOf[Middle]

  def _main() = {
    bad(Bottom(42))
    0
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

