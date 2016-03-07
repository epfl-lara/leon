/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.collection._
import leon.lang._

@isabelle.typ(name = "Nat.nat")
sealed abstract class Nat {

  @isabelle.function(term = "op <=")
  def <=(that: Nat): Boolean = this match {
    case Zero() => true
    case Succ(p) =>
      that match {
        case Zero() => false
        case Succ(q) => p <= q
      }
  }

  @isabelle.function(term = "op +")
  def +(that: Nat): Nat = (this match {
    case Zero() => that
    case Succ(pred) => Succ(pred + that)
  }) ensuring { res =>
    this <= res && that <= res
  }

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

object Nats {

  @isabelle.function(term = "Groups_List.monoid_add_class.listsum")
  def listSum(xs: List[Nat]): Nat = xs match {
    case Nil() => Zero()
    case Cons(x, xs) => x + listSum(xs)
  }

  @isabelle.function(term = "length")
  def length[A](xs: List[A]): Nat = xs match {
    case Nil() => Zero()
    case Cons(x, xs) => Succ(length(xs))
  }

  @isabelle.script(
    name = "Map_Fst_Zip",
    source = "declare map_fst_zip[simp del]"
  )
  @isabelle.proof(method = """(clarsimp, induct rule: list_induct2, auto)""")
  def mapFstZip[A, B](xs: List[A], ys: List[B]) = {
    require(length(xs) == length(ys))
    xs.zip(ys).map(_._1)
  } ensuring { _ == xs }

  def addCommute(x: Nat, y: Nat) =
    (x + y == y + x).holds

  def sumReverse(xs: List[Nat]) =
    (listSum(xs) == listSum(xs.reverse)).holds

  def sumZero[A](xs: List[A]) =
    (listSum(xs.map(_ => Zero())) == Zero()).holds

  @isabelle.proof(method = """(induct "<var xs>", auto)""")
  def sumConstant[A](xs: List[A], k: Nat) =
    (listSum(xs.map(_ => k)) == length(xs) * k).holds

}
