/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._
import leon._

object Hole1 {
  def largestInt(a: Int, b: Int)(implicit o: Oracle[Boolean]) = {
    ?(a, b)
  } ensuring { r => r >= b && r >= a }
}
