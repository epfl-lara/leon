/* Copyright 2009-2016 EPFL, Lausanne */

import leon._
import leon.collection._
import leon.lang._

object TypesWrong {

  case class Data(xs: Array[Int])

  def truth = true holds

}
