/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.annotation._
import scala.language.implicitConversions

package object lang {
  @ignore
  implicit class BooleanDecorations(val underlying: Boolean) {
    def holds : Boolean = {
      assert(underlying)
      underlying
    }
    def ==> (that: Boolean): Boolean = {
      !underlying || that
    }
  }

  @ignore
  object InvariantFunction {
    def invariant(x: Boolean): Unit = ()
  }

  @ignore
  implicit def while2Invariant(u: Unit) = InvariantFunction

  @ignore
  def error[T](reason: java.lang.String): T = sys.error(reason)
 
  @ignore
  implicit class Passes[A,B](io : (A,B)) {
    val (in, out) = io
    def passes(tests : A => B ) : Boolean = 
      try { tests(in) == out } catch { case _ : MatchError => true }
  }

}
