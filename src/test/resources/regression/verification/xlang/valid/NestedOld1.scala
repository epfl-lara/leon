/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object NestedOld1 {

  def test(): Int = {
    var counter = 0

    def inc(): Unit = {
      counter += 1
    } ensuring(_ => counter == old(counter) + 1)

    inc()
    counter
  } ensuring(_ == 1)

}
