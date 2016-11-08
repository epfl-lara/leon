/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object OptionFromLib {
  case class Dummy1(val x: Int)
  case class Dummy2(val opt: Option[Int])

  def foo(x: Int): Option[Int] = {
    require(x >= 0)
    if (x % 2 == 1) Some(x)
    else            None[Int]
  }

  def bar(x: Int): Option[Dummy1] = {
    require(x >= 0)
    if (x % 2 != 0) Some(Dummy1(x))
    else            None[Dummy1]
  }

  def baz(opt: Option[Int]): Dummy2 = {
    Dummy2(opt)
  }

  def funnyTwice(x: Int) = Some(x + x)

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

  // Below we test the inlining of several methods

  def testGetOrElse(): Int = {
    Some(5) getOrElse { 6 }
  } ensuring { _ == 5 }

  def testOrElse(x: Int): Int = {
    require(x >= 0 && x < 2147483646)
    foo(x) orElse { foo(x + 1) } get
  } ensuring { res =>
    ((x % 2 == 1) ==> (res == x)) &&
    ((x % 2 == 0) ==> (res == x + 1))
  }

  def testMap(x: Int): Int = {
    funnyTwice(x) map { y: Int => y + x } get
  } ensuring { _ == x * 3 }

  def testFlatMap(x: Int): Int = {
    funnyTwice(x) flatMap { y => funnyTwice(y) } get
  } ensuring { _ == x * 4 }

  def testFilter(x: Int): Int = {
    funnyTwice(x) filter { _ % 2 == 0 } get
  } ensuring { _ == 2 * x }

  def testWithFilter(x: Int): Int = {
    funnyTwice(x) withFilter { _ % 2 == 0 } get
  } ensuring { _ == 2 * x }

  def testForall(x: Int): Int = {
    if (funnyTwice(x) forall { _ % 2 == 0 }) 0
    else 1
  } ensuring { _ == 0 }

  def testExists(x: Int): Int = {
    if (funnyTwice(x) exists { _ % 2 == 0 }) 0
    else 1
  } ensuring { _ == 0 }

  def _main() = {
    test1() +
    test2() +
    test3() +
    (testGetOrElse() - 5) +
    (testOrElse(0) - 1) +
    (testOrElse(1) - 1) +
    (testMap(0)) +
    (testMap(2) - 6) +
    (testFlatMap(3) - 12) +
    (testFilter(0)) +
    (testFilter(-1) + 2) +
    (testWithFilter(-50) + 100) +
    (testForall(42)) +
    (testExists(58))
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

