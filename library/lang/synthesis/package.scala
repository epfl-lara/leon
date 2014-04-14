/* Copyright 2009-2014 EPFL, Lausanne */

package leon.lang

import leon.annotation._

package object synthesis {
  @ignore
  private def noImpl = throw new RuntimeException("Implementation not supported")

  @ignore
  def choose[A](predicate: A => Boolean): A = noImpl
  @ignore
  def choose[A, B](predicate: (A, B) => Boolean): (A, B) = noImpl
  @ignore
  def choose[A, B, C](predicate: (A, B, C) => Boolean): (A, B, C) = noImpl
  @ignore
  def choose[A, B, C, D](predicate: (A, B, C, D) => Boolean): (A, B, C, D) = noImpl
  @ignore
  def choose[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean): (A, B, C, D, E) = noImpl

  @library
  def ???[T](implicit o: Oracle[T]): T = o.head

  @library
  def ?[T](e1: T)(implicit o1: Oracle[Boolean], o2: Oracle[T]): T = if(???[Boolean](o1)) e1 else ???[T](o2)

  @ignore
  def ?[T](e1: T, es: T*)(implicit o: Oracle[Boolean]): T = noImpl

  @ignore
  def withOracle[A, R](body: Oracle[A] => R): R = noImpl
}
