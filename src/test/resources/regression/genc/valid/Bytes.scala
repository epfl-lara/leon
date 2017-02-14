/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Bytes {

  def fun() = {
    val b: Byte = 127
    test(b) == 0
  }.holds

  def test(b: Byte) = {
    require(b % 2 != 0)
    if (b > 0) 0 else 1
  }

  def bar(x: Int) = {
    require(x < 128)
    x
  }

  def gun(b: Byte): Int = {
    assert(b >= -128 && b <= 127) // this is not a require!
    bar(b)
  }

  def hun(i: Int) = bar(i.toByte)

  def iun(b: Byte, c: Byte) = {
    b + c
  } ensuring { res => -256 <= res && res <= 254 }

  def _main(): Int = {
    if (fun()) {
      if (gun(42) == 42) {
        if (hun(256 + 58) == 58) {
          if (iun(-10, 10) == 0) {

            val b1: Byte = 0x01
            val b2: Byte = 0x03
            val or: Byte = (b1 | b2).toByte
            val and: Byte = (b1 & b2).toByte
            val xor: Byte = (b1 ^ b2).toByte
            val neg: Byte = (~b1).toByte

            if (or == 0x03 && and == 0x01 && xor == 0x02 && neg == -0x02) 0
            else 1

          } else 4
        } else 3
      } else 2
    } else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]) = _main()

}

