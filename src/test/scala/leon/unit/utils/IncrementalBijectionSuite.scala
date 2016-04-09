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

}
