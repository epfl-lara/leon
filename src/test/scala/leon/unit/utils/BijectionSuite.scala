/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.utils._
import org.scalatest._

class BijectionSuite extends FunSuite {

  test("Empty Bijection returns None") {
    val b = new Bijection[Int, Int]
    assert(b.getA(0) === None)
    assert(b.getA(1) === None)
    assert(b.getB(0) === None)
    assert(b.getB(1) === None)
  }

  test("Bijection with one element works both way") {
    val b = new Bijection[Int, Int]
    b += (12 -> 33)

    assert(b.getA(33) === Some(12))
    assert(b.getA(1) === None)
    assert(b.getB(12) === Some(33))
    assert(b.getB(1) === None)
  }

  test("Bijection latest update prevails") {
    val b = new Bijection[Int, Int]
    b += (12 -> 33)
    b += (12 -> 34)

    assert(b.getB(1) === None)
    assert(b.getB(12) === Some(34))
  }

  test("Bijection latest update should delete all previous existing mappings") {
    val b = new Bijection[Int, Int]
    b += (12 -> 33)
    b += (12 -> 34)

    assert(b.getB(12) === Some(34))
    assert(b.getA(34) === Some(12))
    assert(b.getA(33) === None)

    val b2 = new Bijection[Int, Int]
    b2 += (12 -> 33)
    b2 += (11 -> 33)

    assert(b2.getB(12) === None)
    assert(b2.getB(11) === Some(33))
    assert(b2.getA(33) === Some(11))
  }

  test("multiple mixed updates should maintain the invariant") {
    val b = new Bijection[Int, Int]
    b += (12 -> 33)
    b += (13 -> 34)
    b += (12 -> 34)
    b += (11 -> 33)
    b += (13 -> 32)

    assert(b.getB(12) === Some(34))
    assert(b.getB(13) === Some(32))
    assert(b.getB(11) === Some(33))
    assert(b.getA(34) === Some(12))
    assert(b.getA(32) === Some(13))
    assert(b.getA(33) === Some(11))
  }

  test("get or else is working") {
    val b = new Bijection[Int, Int]
    b += (12 -> 33)

    assert(b.getBorElse(12, 15) === 33)
    assert(b.getBorElse(11, 15) === 15)
    assert(b.getAorElse(12, 15) === 15)
    assert(b.getAorElse(30, 10) === 10)
    assert(b.getAorElse(33, 15) === 12)
  }

  test("swap of empty bijection returns an empty bijection") {
    val b = new Bijection[Int, Int]
    val c = b.swap

    assert(b.getB(12) === None)
    assert(c.getB(12) === None)
    assert(b.getB(0) === None)
    assert(c.getB(0) === None)
    assert(b.getA(12) === None)
    assert(c.getA(12) === None)
    assert(b.getA(0) === None)
    assert(c.getA(0) === None)
  }

  test("swap simple bijection is working") {
    val b = new Bijection[Int, Int]
    b += (1 -> 10)
    b += (2 -> 20)
    val c = b.swap

    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === Some(20))
    assert(b.getB(10) === None)
    assert(b.getB(20) === None)
    assert(b.getA(10) === Some(1))
    assert(b.getA(20) === Some(2))
    assert(b.getA(1) === None)
    assert(b.getA(2) === None)

    assert(c.getB(1) === None)
    assert(c.getB(2) === None)
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === Some(2))
    assert(c.getA(10) === None)
    assert(c.getA(20) === None)
    assert(c.getA(1) === Some(10))
    assert(c.getA(2) === Some(20))
  }

  test("updates to swapped bijection are visible in original") {
    val b = new Bijection[Int, Int]
    b += (1 -> 10)
    val c = b.swap
    c += (20 -> 2)

    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === Some(20))
    assert(b.getB(10) === None)
    assert(b.getB(20) === None)
    assert(b.getA(10) === Some(1))
    assert(b.getA(20) === Some(2))
    assert(b.getA(1) === None)
    assert(b.getA(2) === None)

    assert(c.getB(1) === None)
    assert(c.getB(2) === None)
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === Some(2))
    assert(c.getA(10) === None)
    assert(c.getA(20) === None)
    assert(c.getA(1) === Some(10))
    assert(c.getA(2) === Some(20))
  }

  test("swap bijection then overrides some mappings") {
    val b = new Bijection[Int, Int]
    b += (1 -> 10)
    b += (2 -> 20)
    val c = b.swap
    b += (1 -> 30)

    assert(b.getB(1) === Some(30))
    assert(b.getB(2) === Some(20))
    assert(b.getB(10) === None)
    assert(b.getB(20) === None)
    assert(b.getB(30) === None)
    assert(b.getA(10) === None)
    assert(b.getA(20) === Some(2))
    assert(b.getA(30) === Some(1))
    assert(b.getA(1) === None)
    assert(b.getA(2) === None)

    assert(c.getB(1) === None)
    assert(c.getB(2) === None)
    assert(c.getB(10) === None)
    assert(c.getB(20) === Some(2))
    assert(c.getB(30) === Some(1))
    assert(c.getA(10) === None)
    assert(c.getA(20) === None)
    assert(c.getA(30) === None)
    assert(c.getA(1) === Some(30))
    assert(c.getA(2) === Some(20))
  }
}
