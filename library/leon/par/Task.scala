/* Copyright 2009-2013 EPFL, Lausanne */

package leon.par

import leon.annotation._

@library
@isabelle.typ(name = "Leon_Types.task")
@isabelle.constructor(name = "Leon_Types.task.Task")
case class Task[A](c: A) {
  def join: A = c
}