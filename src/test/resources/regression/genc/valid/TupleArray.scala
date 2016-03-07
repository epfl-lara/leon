/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object TupleArray {
  def exists(av: (Array[Int], Int)): Boolean = {
    require(av._1.length < 10000)

    var i = 0
    var found = false
    (while (!found && i < av._1.length) {
      found = av._1(i) == av._2
      i = i + 1
    }) invariant (i >= 0 && i < 10000)
    found
  }

  def main = {
    val a = Array(0, 1, 5, -5, 9)
    val e1 = exists((a, 0))
    val e2 = exists((a, -1))
    if (e1 && !e2) 0
    else -1
  } ensuring { _ == 0 }

}

