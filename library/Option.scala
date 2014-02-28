package leon

import leon.annotation._

sealed abstract class Option[T] {
  @verified
  def getOrElse(default: T) = this match {
    case Some(v) => v
    case None()  => default
  }

  @verified
  def orElse(or: Option[T]) = this match {
    case Some(v) => this
    case None() => or
  }

  @verified
  def isEmpty = this match {
    case Some(v) => false
    case None() =>  true
  }

  @verified
  def nonEmpty  = !isEmpty

  @verified
  def isDefined = !isEmpty
}

case class Some[T](v: T) extends Option[T]
case class None[T]() extends Option[T]
