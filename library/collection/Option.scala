/* Copyright 2009-2015 EPFL, Lausanne */

package leon.collection

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


  // Higher-order API
  def map[R](f: T => R) = { this match {
    case None() => None[R]()
    case Some(x) => Some(f(x))
  }} ensuring { _.isDefined == this.isDefined }

  def flatMap[R](f: T => Option[R]) = this match {
    case None() => None[R]()
    case Some(x) => f(x)
  }

  def filter(p: T => Boolean) = this match {
    case Some(x) if p(x) => Some(x)
    case _ => None[T]()
  }

  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean) = this match {
    case Some(x) if !p(x) => false 
    case _ => true
  }

  def exists(p: T => Boolean) = !forall(!p(_))

}

case class Some[T](v: T) extends Option[T]
case class None[T]() extends Option[T]
