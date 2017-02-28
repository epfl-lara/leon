/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object Chaining {

  // Make it mutable to force the usage of references.
  case class Counter(var c: Int) {
    def inc() = Counter(c + 1)
  }

  def foo(c: Int): Int = {
    val counter = Counter(c)
    counter.inc().inc().c
  } ensuring { _ == c + 2 }

  def _main() = foo(-2)

  @extern
  def main(args: Array[String]) = _main()

}

