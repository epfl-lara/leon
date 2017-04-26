/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Aliasing2 {

  case class Counter(var i: Int)

  def foo(t: (Int, Counter)) {
    val (x, c) = t // this should probably be illegal from an aliasing point of view.
    c.i += x

    // Three example of code that might be legal, but are currently not supported:
    // t._2.i += t._1 // illegal, but why?
    // t._2.i = t._1 // illegal as well, but why?
    // t._2.i = 0 // still illegal, but why?
    // Note that these three example do not attempt to make the whole program be correct.
  }

  def _main(): Int = {
    val c = Counter(58)
    foo((42, c)) // here is the issue with GenC: `c` is copied.

    leon.io.StdOut.println(c.i) // Prints 100 on the JVM

    c.i - 100
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

