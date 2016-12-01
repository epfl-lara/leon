package leon

import annotation.extern

package object grammar {
  @extern
  def variable[A]: A = ???

  @extern
  def selector[A, B](a: A): B = ???

  @extern
  def constructor[A]: A = ???

  @extern
  def closure[A]: A = ???
}
