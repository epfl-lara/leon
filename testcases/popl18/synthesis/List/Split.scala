/* Copyright 2009-2015 EPFL, Lausanne */

import leon.annotation.grammar._
import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar.Grammar._
import leon.collection._

object Split {

  def splitSpec[A](list : List[A], res : (List[A],List[A])) : Boolean = {
    val (l1, l2) = res
    val s1 = l1.size
    val s2 = l2.size
    abs(s1 - s2) <= 1 && s1 + s2 == list.size &&
    l1.content ++ l2.content == list.content
  }

  def abs(i : BigInt) : BigInt = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def split[A](list : List[A]) : (List[A],List[A]) = {
    choose { (res : (List[A],List[A])) => splitSpec(list, res) }
  }
  /*
  def split(list : List) : (List,List) = {
    list match {
      case Nil => (Nil, Nil)
      case Cons(h, t) =>
        val (r1, r2) = split(t)
        (r2, Cons(h, r1))
    }
  } ensuring { (res : (List,List)) =>
    splitSpec(list, res)
  }*/
}
