/* Copyright 2009-2014 EPFL, Lausanne */

import leon._
import leon.lang._
import leon.annotation._

object Numerical {
  def power(base: Int, p: Int): Int = {
    require(p >= 0)
    if (p == 0) {
      1
    } else if (p%2 == 0) {
      power(base*base, p/2)
    } else {
      base*power(base, p-1)
    }
  } ensuring {
    res => ((base, p), res) passes {
      case (_, 0) => 1
      case (b, 1) => b
      case (2, 7) => 128
      case (2, 10) => 1024
    }
  }

  def gcd(a: Int, b: Int): Int = {
    require(a > 0 && b > 0);

    if (a == b) {
      1 // fixme: should be a
    } else if (a > b) {
      gcd(a-b, b)
    } else {
      gcd(a, b-a)
    }
  } ensuring {
    res => (a%res == 0) && (b%res == 0) && (((a,b), res) passes {
      case (120, 24) => 12
      case (5, 7)    => 1
      case (5, 5)    => 5
    })
  }
}
