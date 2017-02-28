/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.annotation._
import scala.language.implicitConversions

package object lang {
  import leon.proof._

  @isabelle.typ(name = "Leon_Types.boolean_decorations")
  @isabelle.constructor(name = "Leon_Types.boolean_decorations.Boolean_Decorations")
  implicit class BooleanDecorations(val underlying: Boolean) {
    @inline
    def holds : Boolean = {
      underlying
    } ensuring {
      (res: Boolean) => res
    }
    @inline
    def holds(becauseOfThat: Boolean) = {
      underlying
    } ensuring {
      (res: Boolean) => becauseOfThat && res
    }

    @inline
    def ==>(that: => Boolean): Boolean = {
      if (underlying) that else true
    }
  }
  @inline def because(b: Boolean) = b

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
  def old[T](value: T): T = sys.error("Can't execute old annotation")

  @ignore
  implicit class Passes[A,B](io : (A,B)) {
    val (in, out) = io
    def passes(tests : A => B ) : Boolean =
      try { tests(in) == out } catch { case _ : MatchError => true }
  }

  @ignore
  def byExample[A, B](in: A, out: B): Boolean = {
    sys.error("Can't execute by example proposition")
  }

  /**
   * A construct for specifying ranking function.
   */
  @library
  def decreases(rankFun: BigInt): Unit = {
    // no-op (rankFun will be ignored in the actual execution)
  }

  @isabelle.typ(name = "Leon_Types.specs_decorations")
  @isabelle.constructor(name = "Leon_Types.specs_decorations.Specs_Decorations")
  implicit class SpecsDecorations[A](val underlying: A) {
    @ignore
    def computes(target: A) = {
      underlying
    } ensuring {
      res => res == target
    }

    @ignore // Programming by example: ???[String] ask input
    def ask[I](input : I) = {
      underlying
    } ensuring {
      (res: A) => byExample(input, res)
    }
  }

  @isabelle.typ(name = "Leon_Types.string_decorations")
  @isabelle.constructor(name = "Leon_Types.string_decorations.String_Decorations")
  implicit class StringDecorations(val underlying: String) {
    @ignore @inline
    def bigLength() = BigInt(underlying.length)
    @ignore @inline
    def bigSubstring(start: BigInt): String = underlying.substring(start.toInt)
    @ignore @inline
    def bigSubstring(start: BigInt, end: BigInt): String = underlying.substring(start.toInt, end.toInt)
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

  @library
  def tupleToString[A, B](t: (A, B), mid: String, f: A => String, g: B => String) = {
    f(t._1) + mid + g(t._2)
  }

  @library
  case class Mutable[T]()
  @library
  implicit def mutable[T] = new Mutable[T]

  @ignore
  def arrayForall[A](array: Array[A], pred: A => Boolean): Boolean = ???
  @ignore
  def arrayForall[A](array: Array[A], from: Int, to: Int, pred: A => Boolean): Boolean = ???
  @ignore
  def arrayExists[A](array: Array[A], pred: A => Boolean): Boolean = ???
  @ignore
  def arrayExists[A](array: Array[A], from: Int, to: Int, pred: A => Boolean): Boolean = ???

  @ignore
  def boundedForall(from: BigInt, to: BigInt, pred: BigInt => Boolean): Boolean = ???
  @ignore
  def boundedForall(from: Int, to: Int, pred: Int => Boolean): Boolean = ???
  @ignore
  def boundedExists(from: BigInt, to: BigInt, pred: BigInt => Boolean): Boolean = ???
  @ignore
  def boundedExists(from: Int, to: Int, pred: Int => Boolean): Boolean = ???

}
