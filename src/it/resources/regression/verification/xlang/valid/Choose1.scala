/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.lang.synthesis._

object Choose1 {

  def test(x: Int): Int = {

    choose((y: Int) => {
      val z = y + 2
      z == y
    })

  } ensuring(_ == x + 2)

}
