/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object UglyArrayUpdate {

  def _main() = {
    val a = Array(0, 1, 2, 3)
    val b = Array(9, 9, 9)
    var c = 666
    val i = 9
    (if (i != 9) b else { c = 0; a })(if (i == 9) { c = c + 1; 0 } else 1) = { c = c * 2; c }

    if (a(0) == 2) 0
    else 1
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

