/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.collection._
import leon.lang._
import leon.math._

object Nats {

  @isabelle.function(term = "Groups_List.monoid_add_class.sum_list")
  def listSum(xs: List[Nat]): Nat = xs match {
    case Nil() => Zero()
    case Cons(x, xs) => x + listSum(xs)
  }

  @isabelle.function(term = "List.length")
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
