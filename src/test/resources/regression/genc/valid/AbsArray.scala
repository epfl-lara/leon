/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object AbsArray {
  def main = {
    val a = Array(0, -1, 2, -3)

    def abs() {
      require(a.length < 10000)

      var i = 0;
      (while (i < a.length && i < 10000) {
        a(i) = if (a(i) < 0) -a(i) else a(i)
        i = i + 1
      }) invariant (i >= 0 && i <= 10000)
    }

    abs()

    a(0) + a(1) - 1 + a(2) - 2 + a(3) - 3 // == 0
  } ensuring { _ == 0 }
}


