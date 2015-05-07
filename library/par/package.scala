/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.lang._
import leon.lang.synthesis.choose

package object par {

  // @library
  def parallel[A,B](x: => A, y: => B) : (A,B) = {
    (x,y)
  }

  case class Task[A](c: A) {
    def join: A = c
  }

  // @library
  def task[A](c: A) = Task(c)
}
