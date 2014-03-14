/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object ComplexChains {
  
  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def f1(list: List): List = list match {
    case Cons(head, tail) if head > 0 => f2(Cons(1, list))
    case Cons(head, tail) if head < 0 => f3(Cons(-1, list))
    case Cons(head, tail) => f1(tail)
    case Nil() => Nil()
  }

  def f2(list: List): List = f3(Cons(0, list))

  def f3(list: List): List = f1(list match {
    case Cons(head, Cons(head2, Cons(head3, tail))) => tail
    case Cons(head, Cons(head2, tail)) => tail
    case Cons(head, tail) => tail
    case Nil() => Nil()
  })
}

// vim: set ts=4 sw=4 et:
