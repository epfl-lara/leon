/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.synthesis
import leon.test._

import leon.synthesis.Algebra._

class AlgebraSuite extends LeonTestSuite {

  test("remainder") { ctx =>
    assert(remainder(1,1) === 0)
    assert(remainder(2,2) === 0)
    assert(remainder(2,1) === 0)
    assert(remainder(0,1) === 0)
    assert(remainder(0,4) === 0)
    assert(remainder(1,3) === 1)
    assert(remainder(1,8) === 1)
    assert(remainder(4,2) === 0)
    assert(remainder(17,3) === 2)
    assert(remainder(25,5) === 0)
    assert(remainder(26,5) === 1)
    assert(remainder(29,5) === 4)

    assert(remainder(1,-1) === 0)
    assert(remainder(-1,1) === 0)
    assert(remainder(2,-2) === 0)
    assert(remainder(-2,-2) === 0)
    assert(remainder(-2,1) === 0)
    assert(remainder(0,-1) === 0)
    assert(remainder(1,-2) === 1)
    assert(remainder(-1,2) === 1)
    assert(remainder(-1,3) === 2)
    assert(remainder(-1,-3) === 2)
    assert(remainder(1,-3) === 1)
    assert(remainder(17,-3) === 2)
    assert(remainder(-25,5) === 0)
  }

  test("divide") { ctx =>
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

    assert(divide(1,-1) === (-1, 0))
    assert(divide(-1,1) === (-1, 0))
    assert(divide(2,-2) === (-1, 0))
    assert(divide(-2,-2) === (1, 0))
    assert(divide(-2,1) === (-2, 0))
    assert(divide(0,-1) === (0, 0))
    assert(divide(1,-2) === (0, 1))
    assert(divide(-1,2) === (-1, 1))
    assert(divide(-1,3) === (-1, 2))
    assert(divide(-1,-3) === (1, 2))
    assert(divide(1,-3) === (0, 1))
    assert(divide(17,-3) === (-5, 2))
    assert(divide(-25,5) === (-5, 0))
  }

  test("binary gcd") { ctx =>
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
    assert(gcd(0,41) === 41)
    assert(gcd(4,0) === 4)

    assert(gcd(-4,0) === 4)
    assert(gcd(-23,41) === 1)
    assert(gcd(23,-41) === 1)
    assert(gcd(-23,-41) === 1)
    assert(gcd(2,-12) === 2)
    assert(gcd(-4,10) === 2)
    assert(gcd(-4,-8) === 4)
  }

  test("n-ary gcd") { ctx =>
    assert(gcd(1,1,1) === 1)
    assert(gcd(1,3,5) === 1)
    assert(gcd(3,1,2) === 1)
    assert(gcd(3,3,3) === 3)
    assert(gcd(4,3,8,6) === 1)
    assert(gcd(5,3,2) === 1)
    assert(gcd(6,3,9) === 3)
    assert(gcd(6,3,8) === 1)
    assert(gcd(2,12,16,4) === 2)
    assert(gcd(4,10,8,22) === 2)
    assert(gcd(10,4,20) === 2)
    assert(gcd(12,8,4) === 4)
    assert(gcd(12,8,2) === 2)
    assert(gcd(12,8,6) === 2)
    assert(gcd(23,41,11) === 1)
    assert(gcd(2,4,8,12,16,4) === 2)
    assert(gcd(2,4,8,11,16,4) === 1)
    assert(gcd(6,3,8, 0) === 1)
    assert(gcd(2,12, 0,16,4) === 2)

    assert(gcd(-12,8,6) === 2)
    assert(gcd(23,-41,11) === 1)
    assert(gcd(23,-41, 0,11) === 1)
    assert(gcd(2,4,-8,-12,16,4) === 2)
    assert(gcd(-2,-4,-8,-11,-16,-4) === 1)
  }

  test("seq gcd") { ctx =>
    assert(gcd(Seq(1)) === 1)
    assert(gcd(Seq(4)) === 4)
    assert(gcd(Seq(7)) === 7)
    assert(gcd(Seq(1,1,1)) === 1)
    assert(gcd(Seq(1,3,5)) === 1)
    assert(gcd(Seq(3,1,2)) === 1)
    assert(gcd(Seq(3,3,3)) === 3)
    assert(gcd(Seq(4,3,8,6)) === 1)
    assert(gcd(Seq(5,3,2)) === 1)
    assert(gcd(Seq(6,3,9)) === 3)
    assert(gcd(Seq(6,3,8)) === 1)
    assert(gcd(Seq(2,12,16,4)) === 2)
    assert(gcd(Seq(4,10,8,22)) === 2)
    assert(gcd(Seq(10,4,20)) === 2)
    assert(gcd(Seq(12,8,4)) === 4)
    assert(gcd(Seq(12,8,2)) === 2)
    assert(gcd(Seq(12,8,6)) === 2)
    assert(gcd(Seq(23,41,11)) === 1)
    assert(gcd(Seq(2,4,8,12,16,4)) === 2)
    assert(gcd(Seq(2,4,8,11,16,4)) === 1)
    assert(gcd(Seq(6,3,8, 0)) === 1)
    assert(gcd(Seq(2,12, 0,16,4)) === 2)

    assert(gcd(Seq(-1)) === 1)
    assert(gcd(Seq(-7)) === 7)
    assert(gcd(Seq(-12,8,6)) === 2)
    assert(gcd(Seq(23,-41,11)) === 1)
    assert(gcd(Seq(23,-41, 0,11)) === 1)
    assert(gcd(Seq(2,4,-8,-12,16,4)) === 2)
    assert(gcd(Seq(-2,-4,-8,-11,-16,-4)) === 1)
  }

  test("binary lcm") { ctx =>
    assert(lcm(1,3) === 3)
    assert(lcm(1,1) === 1)
    assert(lcm(0,1) === 0)
    assert(lcm(2,3) === 6)
    assert(lcm(4,3) === 12)
    assert(lcm(4,6) === 12)
    assert(lcm(8,6) === 24)
  }
  test("n-ary lcm") { ctx =>
    assert(lcm(1,2,3) === 6)
    assert(lcm(1,2,3,4) === 12)
    assert(lcm(5,2,3,4) === 60)
  }
  test("seq lcm") { ctx =>
    assert(lcm(Seq(1,2,3)) === 6)
    assert(lcm(Seq(1,2,3,4)) === 12)
    assert(lcm(Seq(5,2,3,4)) === 60)
  }

  def checkExtendedEuclid(a: Int, b: Int) {
    val (x, y) = extendedEuclid(a, b)
    assert(x*a + y*b === gcd(a, b))
  }

  test("extendedEuclid") { ctx =>
    checkExtendedEuclid(1, 1)
    checkExtendedEuclid(3, 1)
    checkExtendedEuclid(1, 2)
    checkExtendedEuclid(1, 15)
    checkExtendedEuclid(4, 1)
    checkExtendedEuclid(4, 3)
    checkExtendedEuclid(12, 23)
    checkExtendedEuclid(11, 10)
    checkExtendedEuclid(10, 15)

    checkExtendedEuclid(-1, 1)
    checkExtendedEuclid(-1, -1)
    checkExtendedEuclid(3, -1)
    checkExtendedEuclid(-3, -1)
    checkExtendedEuclid(-3, 1)
    checkExtendedEuclid(1, -2)
    checkExtendedEuclid(-1, 2)
    checkExtendedEuclid(-1, -2)
    checkExtendedEuclid(12, -23)
    checkExtendedEuclid(-11, 10)
    checkExtendedEuclid(10, -15)
  }
}

// vim: set ts=4 sw=4 et:
