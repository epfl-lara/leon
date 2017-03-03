/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object DefaultParameter {

  def foo(x: Int = 1) = x

  def bar = foo() + foo(2) == 3

  def _main() = if (bar) 0 else 1

  @extern
  def main(args: Array[String]): Unit = _main()

}

