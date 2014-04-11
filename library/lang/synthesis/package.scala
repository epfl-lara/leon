/* Copyright 2009-2014 EPFL, Lausanne */

package leon.lang

import leon.annotation._

package object synthesis {
  @ignore
  private def noChoose = throw new RuntimeException("Implementation not supported")

  @ignore
  def choose[A](predicate: A => Boolean): A = noChoose
  @ignore
  def choose[A, B](predicate: (A, B) => Boolean): (A, B) = noChoose
  @ignore
  def choose[A, B, C](predicate: (A, B, C) => Boolean): (A, B, C) = noChoose
  @ignore
  def choose[A, B, C, D](predicate: (A, B, C, D) => Boolean): (A, B, C, D) = noChoose
  @ignore
  def choose[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean): (A, B, C, D, E) = noChoose

  @library
  def ???[T](implicit o: Oracle[T]): T = o.head

  @library
  def ?[T](e1: T)(implicit o: Oracle[Boolean], o2: Oracle[T]): T = if(???[Boolean]) e1 else ???[T]

  @ignore
  def ?[T](e1: T, es: T*)(implicit o: Oracle[Boolean]): T = noChoose
}
