package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import invariant._

/*  def app[U, T](f: U => T, x: U): T = {
    f(x)
  } ensuring { _ =>
    val in = inState[Unit]
    time <= ? * time(f(x) withState in) + ?
  }
*/
// Higher-order API
sealed abstract class List[T] {

  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def length = size

  /**
   * A function that is the sum of time taken by 'f' when applied over the elements of the list.
   * Note: here `f` can update state.
   */
  def listTime[R](f: T => R, st: Set[Fun[R]]): BigInt = {
    this match {
      case Nil() => 0
      case Cons(x, t) =>
        time(f(x) withState st) + t.listTime(f, st)
    }
  }

  def map[R](f: T => R): List[R] = { this match {
    case Nil() => Nil[R]()
    case Cons(h, t) => Cons(f(h), t.map(f))
  }} ensuring {
    val in = inState[R]
    time <= ? * listTime(f, in) + ?
  }

  /*def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  def scanLeft[R](z: R)(f: (R,T) => R): List[R] = { this match {
    case Nil() => z :: Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def flatMap[R](f: T => List[R]): List[R] =
    ListOps.flatten(this map f)

  def filter(p: T => Boolean): List[T] = { this match {
    case Nil() => Nil[T]()
    case Cons(h, t) if p(h) => Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def groupBy[R](f: T => R): Map[R, List[T]] = this match {
    case Nil() => Map.empty[R, List[T]]
    case Cons(h, t) =>
      val key: R = f(h)
      val rest: Map[R, List[T]] = t.groupBy(f)
      val prev: List[T] = if (rest isDefinedAt key) rest(key) else Nil[T]()
      (rest ++ Map((key, h :: prev))) : Map[R, List[T]]
  }*/
}

case class Cons[T](h: T, t: List[T]) extends List[T]

case class Nil[T]() extends List[T]
