/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object Generics3 {
  case class Dummy[T](t: T)

  def fun[T](t: Option[T]): Option[Dummy[T]] = {
    if (t.isDefined) Some(Dummy(t.get))
    else None[Dummy[T]]
  }

  def test1(): Int = {
    val none = None[Int]
    if (fun(none).isDefined) 1
    else 0
  } ensuring { _ == 0 }

  def test2(): Int = {
    val some = Some[Int](42)
    val res = fun(some)
    if (res.isDefined && res.get.t == 42) 0
    else 1
  } ensuring { _ == 0 }

  def _main() = {
    test1() + test2()
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

