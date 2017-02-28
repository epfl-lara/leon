/* Copyright 2009-2016 EPFL, Lausanne */

package leon.math

import leon.annotation._
import leon.collection._
import leon.lang._

@library
@isabelle.typ(name = "Nat.nat")
sealed abstract class Nat {

  @library
  @isabelle.function(term = "int")
  def toBigInt: BigInt = this match {
    case Zero() => 0
    case Succ(p) => 1 + p.toBigInt
  }

  @library
  @isabelle.function(term = "op <=")
  def <=(that: Nat): Boolean = this match {
    case Zero() => true
    case Succ(p) =>
      that match {
        case Zero() => false
        case Succ(q) => p <= q
      }
  }

  @library
  @isabelle.function(term = "op +")
  def +(that: Nat): Nat = this match {
    case Zero() => that
    case Succ(pred) => Succ(pred + that)
  }

  @library
  @isabelle.function(term = "op *")
  def *(that: Nat): Nat = this match {
    case Zero() => Zero()
    case Succ(pred) => that + pred * that
  }

}

@isabelle.constructor(name = "Groups.zero_class.zero")
case class Zero() extends Nat

@isabelle.constructor(name = "Nat.Suc")
case class Succ(pred: Nat) extends Nat
