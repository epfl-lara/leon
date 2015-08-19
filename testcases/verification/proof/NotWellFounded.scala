/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.proof

import leon.collection._
import leon.lang._
import leon.proof._

object NotWellFounded {

  // This proof is not well-founded.  Since Leon doesn't run the
  // termination checker by default, it will accept the proof as
  // valid.
  def allListsAreEmpty[T](xs: List[T]): Boolean = {
    xs.isEmpty because {
      xs match {
        case Nil()       => trivial
        case Cons(x, xs) => allListsAreEmpty(x :: xs)
      }
    }
  }.holds
}
