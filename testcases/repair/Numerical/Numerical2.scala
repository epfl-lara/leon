/* Copyright 2009-2015 EPFL, Lausanne */

import leon._
import leon.lang._
import leon.annotation._

object Numerical {
  def power(base: BigInt, p: BigInt): BigInt = {
    require(p >= BigInt(0))
    if (p == BigInt(0)) {
      BigInt(1)
    } else if (p%BigInt(2) == BigInt(0)) {
      power(base*base, p/BigInt(2))
    } else {
      base*power(base, p-BigInt(1))
    }
  } ensuring {
    res => ((base, p), res) passes {
      case (_, BigInt(0)) => BigInt(1)
      case (b, BigInt(1)) => b
      case (BigInt(2), BigInt(7)) => BigInt(128)
      case (BigInt(2), BigInt(10)) => BigInt(1024)
    }
  }

  def gcd(a: BigInt, b: BigInt): BigInt = {
    require(a > BigInt(0) && b > BigInt(0));

    if (a == b) {
      BigInt(1) // fixme: should be a
    } else if (a > b) {
      gcd(a-b, b)
    } else {
      gcd(a, b-a)
    }
  } ensuring {
    res => (a%res == BigInt(0)) && (b%res == BigInt(0)) && (((a,b), res) passes {
      case (BigInt(120), BigInt(24)) => BigInt(12)
      case (BigInt(5), BigInt(7))    => BigInt(1)
      case (BigInt(5), BigInt(5))    => BigInt(5)
    })
  }
}
