/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.{ extern, inline }

object Inlining {
  sealed abstract class Option[T] {
    @inline
    def map[U](f: T => U): Option[U] = this match {
      case Some(x) => Some(f(x))
      case None() => None()
    }
  }

  case class Some[T](x: T) extends Option[T]

  case class None[T]() extends Option[T]

  def test1(): Int = {
    def twice(opt: Option[Int]): Option[Int] = opt map { x => x * 2 }

    twice(Some(4)) match {
      case Some(8) => 0
      case _ => -2
    }
  } ensuring { res => res == 0 }

  def test2(): Int = {
    var v = -1

    def twice(opt: Option[Int]): Option[Int] = opt map { x => v = v + 1; x * 2 }

    twice(Some(4)) match {
      case Some(8) => v
      case _ => -2
    }
  } ensuring { res => res == 0 }

  def _main() = {
    test1() + test2()
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

