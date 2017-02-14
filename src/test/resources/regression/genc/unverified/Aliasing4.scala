/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Aliasing4 {

  case class MutableInteger(var x: Int)

  def selector(first: Boolean, i: MutableInteger, j: MutableInteger) {
    /* // This is simple because no normalisation is needed:
     * if (first) mutate(i)
     * else mutate(j)
     */

    // This is no longer trivial but doable:
    mutate(if (first) i else j)
  }

  def mutate(m: MutableInteger) {
    m.x = 0
  }

  def _main(): Int = {
    val a = MutableInteger(42)
    val b = MutableInteger(58)

    selector(first = true, a, b)

    if (a.x == 0) {
      if (b.x == 58) 0
      else 2
    } else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

