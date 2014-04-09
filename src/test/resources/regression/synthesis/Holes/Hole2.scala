/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._
import leon._

object Hole2 {
  def genList()(implicit o: Oracle[Boolean]): List[Int] = ?(Nil[Int](), Cons[Int](0, genList()(o.right)))

  def listOfSize2(implicit o: Oracle[Boolean]) = {
    genList()
  } ensuring {
    _.size == 2
  }
}
