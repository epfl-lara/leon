package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

object SimpleHOListLibrary {

  def app[U, T](f: U => T, x: U): T = {
    f(x)
  } ensuring{_ =>
    val in = inState[Unit]
    time <= ? * time(f(x) withState in) + ?
  }

  def map[U, T](f: () => T, s: List[U]): List[T] = {
    s match {
      case Nil()         => Nil()
      case Cons(x, tail) => Cons(f(), map(f, tail))
    }
  } //ensuring (_ => time <= ?)
}
