/* Copyright 2009-2014 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Transform {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case object Nil extends List

    def input01(a: Int): Int = {
      val b = 42
      a + b + b
    }

    def output01(a: Int): Int = {
      a + 42 + 42
    }

    def input02(a: Int): Int = {
      val b = 42+a
      a + b
    }

    def output02(a: Int): Int = {
      a + (42 + a)
    }

    def input03(a: Int): Int = {
      val b = 42
      val c = 43

      a + c
    }

    def output03(a: Int): Int = {
      a + 43
    }

    def input04(a: Int): Int = {
      val c = 43 + a

      a + c + c
    }

    def output04(a: Int): Int = {
      val c = 43 + a

      a + c + c
    }
}
