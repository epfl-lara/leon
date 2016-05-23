/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.utils._
import org.scalatest._

class IncrementalBijectionSuite extends FunSuite {

  test("Empty IncrementalBijection returns None") {
    val b = new IncrementalBijection[Int, Int]
    assert(b.getA(0) === None)
    assert(b.getA(1) === None)
    assert(b.getB(0) === None)
    assert(b.getB(1) === None)
  }

  test("IncrementalBijection with one element works both way") {
    val b = new IncrementalBijection[Int, Int]
    b += (12 -> 33)

    assert(b.getA(33) === Some(12))
    assert(b.getA(1) === None)
    assert(b.getB(12) === Some(33))
    assert(b.getB(1) === None)
  }

  test("Latest update prevails") {
    val b = new IncrementalBijection[Int, Int]
    b += (12 -> 33)
    b += (12 -> 34)

    assert(b.getB(1) === None)
    assert(b.getB(12) === Some(34))
    assert(b.getA(34) === Some(12))
    assert(b.getA(33) === None)
  }

  test("push does not forget the past") {
    val b = new IncrementalBijection[Int, Int]
    b += (10 -> 20)
    assert(b.getB(10) === Some(20))
    b.push()
    assert(b.getB(10) === Some(20))
    assert(b.getA(20) === Some(10))
  }

  test("push/pop does not forget the past") {
    val b = new IncrementalBijection[Int, Int]
    b += (10 -> 20)
    assert(b.getB(10) === Some(20))
    assert(b.getA(20) === Some(10))
    b.push()
    b.pop()
    assert(b.getB(10) === Some(20))
    assert(b.getA(20) === Some(10))
  }

  test("Writing after a push is no longer visible after a pop") {
    val b = new IncrementalBijection[Int, Int]
    b += (10 -> 20)
    assert(b.getB(10) === Some(20))
    b.push()
    b += (30 -> 40)
    assert(b.getB(30) === Some(40))
    b.pop()
    assert(b.getB(30) === None)
    assert(b.getA(40) === None)
    //but first frame is still there
    assert(b.getB(10) === Some(20))
    assert(b.getA(20) === Some(10))
  }

  test("Many pushes do not forget the past") {
    val b = new IncrementalBijection[Int, Int]
    b += (10 -> 20)
    assert(b.getB(10) === Some(20))
    b.push()
    b.push()
    b += (30 -> 40)
    b.push()
    b.push()
    assert(b.getB(10) === Some(20))
    assert(b.getA(20) === Some(10))
    assert(b.getB(30) === Some(40))
    assert(b.getA(40) === Some(30))
  }

  test("Multiple mixed updates should maintain the invariant") {
    val b = new IncrementalBijection[Int, Int]
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

  test("Changing the bijection for one element after a push should change its correspondence") {
    val b = new IncrementalBijection[Int, Int]
    b += (12 -> 33)
    assert(b.getB(12) === Some(33))
    assert(b.getA(33) === Some(12))
    b.push()
    b += (11 -> 33)
    assert(b.getB(11) === Some(33))
    assert(b.getA(33) === Some(11))
    assert(b.getB(12) === None)
    b.pop()
    //but when poping the original mapping should be back
    assert(b.getB(12) === Some(33))
    assert(b.getA(33) === Some(12))
  }

  test("swap simple bijection is working") {
    val b = new IncrementalBijection[Int, Int]
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
    val b = new IncrementalBijection[Int, Int]
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
    val b = new IncrementalBijection[Int, Int]
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

  test("Push on a swapped bijection also pushes to original") {
    val b = new IncrementalBijection[Int, Int]
    b += (1 -> 10)
    val c = b.swap
    c.push()
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

  test("Pop on a swapped bijection also pop to original") {
    val b = new IncrementalBijection[Int, Int]
    b += (1 -> 10)
    val c = b.swap
    c.push()
    c += (20 -> 2)

    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === Some(20))
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === Some(2))

    c.pop()
    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === None)
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === None)
  }

  test("push/pop on a swapped bijection stays consistent") {
    val b = new IncrementalBijection[Int, Int]
    b += (1 -> 10)
    val c = b.swap
    c.push()
    c += (20 -> 2)

    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === Some(20))
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === Some(2))

    b.pop()
    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === None)
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === None)

    c += (30 -> 3)
    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === None)
    assert(b.getB(3) === Some(30))
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === None)
    assert(c.getB(30) === Some(3))
  }

  test("overriding mapping in swap bijection is consistent after a pop") {
    val b = new IncrementalBijection[Int, Int]
    b += (1 -> 10)
    b += (2 -> 20)
    val c = b.swap
    c.push()
    c += (30 -> 1)

    assert(b.getB(1) === Some(30))
    assert(b.getB(2) === Some(20))
    assert(c.getB(10) === None)
    assert(c.getB(20) === Some(2))
    assert(c.getB(30) === Some(1))

    c.pop()
    assert(b.getB(1) === Some(10))
    assert(b.getB(2) === Some(20))
    assert(c.getB(10) === Some(1))
    assert(c.getB(20) === Some(2))
    assert(c.getB(30) === None)
  }

}
