/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Test {

  def test(x: Int): Int = {

    choose((y: Int) => {
      val z = y + 2
      z == y
    })

  } ensuring(_ == x + 2)

}
