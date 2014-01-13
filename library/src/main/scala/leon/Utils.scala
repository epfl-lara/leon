/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import  scala.language.implicitConversions

object Utils {
  sealed class IsValid(val property : Boolean) {
    def holds : Boolean = {
      assert(property)
      property
    }
  }

  implicit def any2IsValid(x: Boolean) : IsValid = new IsValid(x)

  def epsilon[A](pred: (A) => Boolean): A = throw new RuntimeException("Implementation not supported")

  object InvariantFunction {
    def invariant(x: Boolean): Unit = ()
  }
  implicit def while2Invariant(u: Unit) = InvariantFunction

  def waypoint[A](i: Int, expr: A): A = expr

  private def noChoose = throw new RuntimeException("Implementation not supported")

  def choose[A](predicate: A => Boolean): A = noChoose
  def choose[A, B](predicate: (A, B) => Boolean): (A, B) = noChoose
  def choose[A, B, C](predicate: (A, B, C) => Boolean): (A, B, C) = noChoose
  def choose[A, B, C, D](predicate: (A, B, C, D) => Boolean): (A, B, C, D) = noChoose
  def choose[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean): (A, B, C, D, E) = noChoose
  
  private def noForall = throw new RuntimeException("Implementation not supported")
  
  def forall[A](predicate: A => Boolean): Boolean = noForall
  def forall[A, B](predicate: (A, B) => Boolean): Boolean = noForall
  def forall[A, B, C](predicate: (A, B, C) => Boolean): Boolean = noForall
  def forall[A, B, C, D](predicate: (A, B, C, D) => Boolean): Boolean = noForall
  def forall[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean): Boolean = noForall
  
  sealed class ImpliesArrowAssoc(val value: Boolean) {
    def ==>(that: Boolean): Boolean = throw new RuntimeException("Implementation not supported")
  }
  implicit def boolean2ImpliesArrowAssoc(b1: Boolean) = new ImpliesArrowAssoc(b1)

  def error[T](reason: String): T = sys.error(reason)
}
