package leon

import leon.Annotations._
import leon.Utils._

object Library {
  /***
   * Lists
   ***/

  sealed abstract class List[T] {
    @verified
    def size: Int = (this match {
      case Nil() => 0
      case Cons(h, t) => 1 + t.size
    }) ensuring (_ >= 0)

    @verified
    def content: Set[T] = this match {
      case Nil() => Set()
      case Cons(h, t) => Set(h) ++ t.content
    }

    @verified
    def contains(v: T): Boolean = (this match {
      case Cons(h, t) if h == v => true
      case Cons(_, t) => t.contains(v)
      case Nil() => false
    }) ensuring { res => res == (content contains v) }

    @verified
    def append(that: List[T]): List[T] = (this match {
      case Nil() => that
      case Cons(x, xs) => Cons(x, xs.append(that))
    }) ensuring { _.content == this.content ++ that.content }

    @verified
    def head: T = {
      require(this != Nil[T]())
      this match {
        case Cons(h, t) => h
      }
    }

    @verified
    def tail: List[T] = {
      require(this != Nil[T]())
      this match {
        case Cons(h, t) => t
      }
    }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  /***
   * Options
   ***/

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
  }
  case class Some[T](v: T) extends Option[T]
  case class None[T]() extends Option[T]


}
