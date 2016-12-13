/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Bytes1 {

  def test(b: Byte) = {
    require(b % 2 != 0)
    if (b > 0) 0 else 1
  }

  def fun(b: Byte) = test(b)

  def gun(b: Byte, c: Byte) = {
    b + c
  } ensuring { res => -128 <= res && res <= 127 }

}

