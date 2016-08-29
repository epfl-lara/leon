/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import leon.annotation._

/**
 * @author Viktor
 */
@library
@isabelle.typ(name = "Sum_Type.sum")
sealed abstract class Either[A,B] {
  def isLeft : Boolean
  def isRight : Boolean
  def swap : Either[B,A]
}
@library
@isabelle.constructor(name = "Sum_Type.Inl")
case class Left[A,B](content: A) extends Either[A,B] {
  def isLeft = true
  def isRight = false
  def swap = Right[B,A](content)
}
@library
@isabelle.constructor(name = "Sum_Type.Inr")
case class Right[A,B](content: B) extends Either[A,B] {
  def isLeft = false
  def isRight = true
  def swap = Left[B,A](content)
}
