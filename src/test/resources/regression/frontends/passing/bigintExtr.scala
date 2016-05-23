/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._

object Test {
  def b(b: List[BigInt]) = b match {
    case Cons(BigInt(42), Nil()) => true
    case _ => false
  }
}
