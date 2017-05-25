/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.annotation._

package object par {

  @library
  @inline
  def parallel[A,B](x: => A, y: => B) : (A,B) = {
    (x,y)
  }

  @library
  def task[A](c: A) = Task(c)
}
