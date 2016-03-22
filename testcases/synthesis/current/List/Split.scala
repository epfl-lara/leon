/* Copyright 2009-2015 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Complete {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def splitSpec(list : List, res : (List,List)) : Boolean = {
    val s1 = size(res._1)
    val s2 = size(res._2)
    abs(s1 - s2) <= 1 && s1 + s2 == size(list) &&
    content(res._1) ++ content(res._2) == content(list) 
  }

  def abs(i : BigInt) : BigInt = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def split(list : List) : (List,List) = {
    choose { (res : (List,List)) => splitSpec(list, res) }
  }

}
