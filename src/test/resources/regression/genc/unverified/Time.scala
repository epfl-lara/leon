/* Copyright 2009-2017 EPFL, Lausanne */

import leon.annotation._
import leon.io.{ StdIn, StdOut }
import leon.util.{ TimePoint }
import leon.lang._

/*
 * This programs tests the Time API and suits no other purposes.
 */
object Time {

  def compute = {
    def slowFib(n: Int): Int = {
      require(n >= 0)
      n match {
        case 0 => 0
        case 1 => 1
        case n => slowFib(n - 1) + slowFib(n - 2)
      }
    }

    var i = 0
    var j = 0
    while (i < 20) {
      val x = slowFib(25)
      val y = slowFib(30)
      val z = slowFib(35)
      j += z - y - x
      i += 1
    }

    j
  }

  def _main() = {
    val t1 = TimePoint.now()

    val data = compute

    val t2 = TimePoint.now()

    val elapsed = TimePoint.elapsedMillis(t1, t2)

    StdOut.print("data = ")
    StdOut.println(data)
    StdOut.print("computed in ")
    StdOut.print(elapsed)
    StdOut.println("ms.")

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

