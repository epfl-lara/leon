/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import leon.annotation._

@library
sealed abstract class Option[T] {

  def get : T = {
    require(this.isDefined)
    this match {
      case Some(x) => x
    }
  }

  def getOrElse(default: T) = this match {
    case Some(v) => v
    case None()  => default
  }

  def orElse(or: Option[T]) = this match {
    case Some(v) => this
    case None() => or
  }

  def isEmpty = this match {
    case Some(v) => false
    case None() =>  true
  }

  def nonEmpty  = !isEmpty

  def isDefined = !isEmpty

}

case class Some[T](v: T) extends Option[T]
case class None[T]() extends Option[T]
