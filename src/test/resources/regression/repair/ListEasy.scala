/* Copyright 2009-2016 EPFL, Lausanne */

package leon.custom

import leon._
import leon.lang._
import leon.annotation._
import leon.collection._

sealed abstract class List0[T] {
  def size: BigInt = (this match {
    case Nil0() => BigInt(0)
    case Cons0(h, t) => BigInt(1) + t.size
  }) ensuring (_ >= 0)

  def content: Set[T] = this match {
    case Nil0() => Set()
    case Cons0(h, t) => Set(h) ++ t.content
  }

  def contains(v: T): Boolean = (this match {
    case Cons0(h, t) if h == v => true
    case Cons0(_, t) => t.contains(v)
    case Nil0() => false
  }) ensuring { res => res == (content contains v) }


  def pad(s: BigInt, e: T): List0[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil0(), s) =>
      Cons0(e, Nil0().pad(s-1, e))
    case (Cons0(h, t), s) =>
      Cons0(h, t.pad(s-1, e)) // FIXME should be s
  }} ensuring { res =>
    ((this,s,e), res) passes {
      case (Cons0(a,Nil0()), BigInt(2), x) => Cons0(a, Cons0(x, Cons0(x, Nil0())))
    }
  }
}

case class Cons0[T](h: T, t: List0[T]) extends List0[T]
case class Nil0[T]() extends List0[T]
