/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._ 
import leon.lang.synthesis._

object Unap {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}

object Unapply {
  def bar(i: Int, b: Boolean): Boolean = (i, b, ()) match {
    case Unap(_, b) if b => b
    case Unap((), b) => 
      choose( (b1: Boolean) => b == b1 == i < 0 )
  }

}
