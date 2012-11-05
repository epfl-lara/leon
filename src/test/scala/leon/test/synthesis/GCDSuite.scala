package leon.test.synthesis

import org.scalatest.FunSuite

import leon.synthesis.GCD._

class GCDSuite extends FunSuite {

  test("divide") {
    assert(divide(1,1) === (1, 0))
    assert(divide(2,2) === (1, 0))
    assert(divide(2,1) === (2, 0))
    assert(divide(0,1) === (0, 0))
    assert(divide(0,4) === (0, 0))
    assert(divide(1,3) === (0, 1))
    assert(divide(1,8) === (0, 1))
    assert(divide(4,2) === (2, 0))
    assert(divide(17,3) === (5, 2))
    assert(divide(25,5) === (5, 0))
    assert(divide(26,5) === (5, 1))
    assert(divide(29,5) === (5, 4))
  }

  test("gcd") {
    assert(gcd(1,1) === 1)
    assert(gcd(1,3) === 1)
    assert(gcd(3,1) === 1)
    assert(gcd(3,3) === 3)
    assert(gcd(4,3) === 1)
    assert(gcd(5,3) === 1)
    assert(gcd(6,3) === 3)
    assert(gcd(2,12) === 2)
    assert(gcd(4,10) === 2)
    assert(gcd(10,4) === 2)
    assert(gcd(12,8) === 4)
    assert(gcd(23,41) === 1)
  }

  def checkExtendedEuclid(a: Int, b: Int) {
    val (x, y) = extendedEuclid(a, b)
    assert(x*a + y*b === gcd(a, b))
  }

  test("extendedEuclid") {
    checkExtendedEuclid(1, 1)
    checkExtendedEuclid(3, 1)
    checkExtendedEuclid(1, 2)
    checkExtendedEuclid(1, 15)
    checkExtendedEuclid(4, 1)
    checkExtendedEuclid(4, 3)
    checkExtendedEuclid(12, 23)
    checkExtendedEuclid(11, 10)
    checkExtendedEuclid(10, 15)
  }
}
