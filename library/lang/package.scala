/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.annotation._
import scala.language.implicitConversions

package object lang {

  implicit class BooleanDecorations(val underlying: Boolean) {
    @inline
    def holds : Boolean = {
      underlying
    } ensuring {
      _ == true
    }

    @inline
    def ==>(that: => Boolean): Boolean = {
      if (underlying) that else true
    }
  }

  implicit class SpecsDecorations[A](val underlying: A) {
    @inline
    def computes(target: A) = {
      underlying
    } ensuring {
      res => res == target
    }
  }

  @ignore def forall[A](p: A => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B](p: (A,B) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C](p: (A,B,C) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C,D](p: (A,B,C,D) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C,D,E](p: (A,B,C,D,E) => Boolean): Boolean = sys.error("Can't execute quantified proposition")

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

  @ignore
  object BigInt {
    def apply(b: Int): scala.math.BigInt = scala.math.BigInt(b)
    def apply(b: String): scala.math.BigInt = scala.math.BigInt(b)

    def unapply(b: scala.math.BigInt): scala.Option[Int] = {
      if(b >= Integer.MIN_VALUE && b <= Integer.MAX_VALUE) {
        scala.Some(b.intValue())
      } else {
        scala.None
      }
    }
  }
  
  @ignore
  object StrOps {
    def concat(a: String, b: String): String = {
      a + b
    }
    def length(a: String): BigInt = {
      BigInt(a.length)
    }
    def substring(a: String, start: BigInt, end: BigInt): String = {
      if(start > end || start >= length(a) || end <= 0) "" else a.substring(start.toInt, end.toInt)
    }
    def bigIntToString(a: BigInt): String = {
      a.toString
    }
    def intToString(a: Int): String = {
      a.toString
    }
    def doubleToString(a: Double): String = {
      a.toString
    }
    def booleanToString(a: Boolean): String = {
      if(a) "true" else "false"
    }
    def charToString(a: Char): String = {
      a.toString
    }
    def realToString(a: Real): String = ???
  }
    
  
}
