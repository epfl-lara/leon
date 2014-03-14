/* Copyright 2009-2014 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Transform {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case object Nil extends List

    def input01(a: List): Int = a match {
      case Cons(h, Cons(th, tt)) =>
        h + th
      case _ =>
        a match {
          case Cons(th, Nil) =>
            th
          case _ =>
            0
        }
    }

    def output01(a: List): Int = a match {
      case Cons(h, Cons(th, _)) =>
        h + th
      case Cons(th, Nil) =>
        th
      case _ =>
        0
    }
    def input02(a: List): Int = a match {
      case Cons(h, t) =>
        t match {
          case Cons(th, tt) => 1
          case Nil => 2
        }
      case Nil =>
        3
    }

    def output02(a: List): Int = a match {
      case Cons(_, Cons(_, _)) => 1
      case Cons(_, Nil) => 2
      case Nil => 3
    }
}
