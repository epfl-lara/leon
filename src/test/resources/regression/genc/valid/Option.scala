/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object Option {
  sealed abstract class Option[T] {
    def get: T = {
      require(isDefined)
      //this match { case Some(x) => x }
      this.asInstanceOf[Some[T]].x // slightly more efficient than pattern matching: no type checking
    }

    def isEmpty = this match {
      case Some(_) => false
      case None() => true
    }

    def nonEmpty = !isEmpty
    def isDefined = nonEmpty
  }

  case class Some[T](x: T) extends Option[T]

  case class None[T]() extends Option[T]

  case class Dummy1(x: Int)
  case class Dummy2(opt: Option[Int])

  def foo(x: Int): Option[Int] = {
    if (x % 2 == 1) Some(x)
    else            None[Int]
  }

  def bar(x: Int): Option[Dummy1] = {
    if (x % 2 != 0) Some(Dummy1(x))
    else            None[Dummy1]
  }

  def baz(opt: Option[Int]): Dummy2 = {
    Dummy2(opt)
  }

  def test1(): Int = {
    val o1 = foo(1)
    val o2 = foo(2)

    if (o1.nonEmpty && o2.isEmpty && o1.get == 1) 0
    else 1
  } ensuring { _ == 0 }

  def test2(): Int = {
    val o1 = bar(1)
    val o2 = bar(2)

    if (o1.nonEmpty && o2.isEmpty && o1.get.x == 1) 0
    else 1
  } ensuring { _ == 0 }

  def test3(): Int = {
    val o = baz(Some(42))

    if (o.opt.isDefined && o.opt.get == 42) 0
    else 1
  } ensuring { _ == 0 }

  def _main() = {
    test1() + test2() + test3()
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

