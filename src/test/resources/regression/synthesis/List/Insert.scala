/* Copyright 2009-2014 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Insert {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
      case Nil => BigInt(0)
      case Cons(_, t) => size(t) + 1
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  //def insert(in1: List, v: Int): List = {
  //  Cons(v, in1)
  //} ensuring { content(_) == content(in1) ++ Set(v) }

  def insert(in1: List, v: Int) = choose {
    (out : List) =>
      content(out) == content(in1) ++ Set(v)
  }
}
