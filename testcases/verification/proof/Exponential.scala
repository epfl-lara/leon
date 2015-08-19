/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.proof

import leon.annotation._
import leon.lang._
import leon.proof._

object Exponential {

  /** A simple, but slow function for computing exponentials. */
  def exp(x: BigInt, y: BigInt): BigInt = {
    require(y >= 0)
    if      (x == 0) 0
    else if (y == 0) 1
    else             x * exp(x, y - 1)
  }

  /** Exponentials of positive numbers are positive. */
  def positive(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x >= 0)
    exp(x, y) >= 0 because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             check {
        x * exp(x, y - 1) >= 0 because positive(x, y - 1)
      }
    }
  }.holds

  /** The exponential function is positive (shorter proof). */
  def positiveShort(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x > 0)
    exp(x, y) >= 0 because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             positiveShort(x, y - 1)
    }
  }.holds

  /**
   * The exponential function (with respect to a fixed base) is a
   * homomorphism between the commutative monoids of addition and
   * multiplication over integers.
   */
  def monoidHom(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    require(y >= 0 && z >= 0)
    exp(x, y + z) == exp(x, y) * exp(x, z) because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             {
        exp(x, y + z)                 ==| (y + z != 0)           |
        x * exp(x, y + z - 1)         ==| monoidHom(x, y - 1, z) |
        x * exp(x, y - 1) * exp(x, z)
      }.qed
    }
  }.holds

  /**
   * Exponentiation (by a fixed exponent) commutes with
   * multiplication.
   */
  def expMultCommute(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    require(z >= 0)
    exp(x * y, z) == exp(x, z) * exp(y, z) because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else if (z == 0) trivial
      else             check {
        x * y * exp(x * y, z - 1) ==
          x * exp(x, z - 1) * y * exp(y, z - 1) because
          expMultCommute(x, y, z - 1)
      }
    }
  }.holds

  /** A combination of the previous two lemmas. */
  def square(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0)
    exp(x, 2 * y) == exp(x * x, y) because
      monoidHom(x, y, y) && expMultCommute(x, x, y)
  }.holds

  /** A more efficient function for computing exponentials. */
  def fastExp(x: BigInt, y: BigInt): BigInt = {
    require(y >= 0)
    if      (x == 0)     0
    else if (y == 0)     1
    else if (y % 2 == 0) fastExp(x * x, y / 2)
    else                 x * fastExp(x, y - 1)
  }

  /**
   * The two versions of the exponential function are equivalent.
   *
   * NOTE: Leon is able to verify most of the individual sub-goals of
   * this correctness proof in fractions of a second using Z3-F, but
   * often times out after >30s when trying to verify the overall
   * post-condition (Intel core i7, Ubuntu 14.04.2 LTS, x86-64,
   * 2015-06-04).
   */
  def fastExpCorrect(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0)
    fastExp(x, y) == exp(x, y) because {
      if      (x == 0)     trivial
      else if (y == 0)     trivial
      else if (y % 2 == 0) {
        val z = y / 2; {
          fastExp(x, y)         ==| trivial                  |
          fastExp(x * x, z)     ==| fastExpCorrect(x * x, z) |
          exp(x * x, z)         ==| square(x, z)             |
          exp(x, y)
        }.qed
      }
      else                 {
        val z = (y - 1) / 2; {
          fastExp(x, y)         ==| (y % 2 != 0)             |
          x * fastExp(x * x, z) ==| {
            fastExp(x * x, z)   ==| fastExpCorrect(x * x, z) |
            exp(x * x, z)       ==| square(x, z)             |
            exp(x, 2 * z)       ==| trivial                  |
            exp(x, y - 1)                              }.qed |
          x * exp(x, y - 1)     ==| (y != 0)                 |
          exp(x, y)
        }.qed
      }
    }
  }.holds

  /**
   * The two versions of the exponential function are equivalent.
   *
   * NOTE: this version of the correctness proof is more verbose but
   * easier to debug.  Leon is able to verify most of the individual
   * sub-goals in fractions of a second using Z3-F, but often times
   * out after >30s when trying to verify the overall post-condition
   * (Intel core i7, Ubuntu 14.04.2 LTS, x86-64, 2015-06-04).
   */
  def fastExpCorrect2(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0)
    fastExp(x, y) == exp(x, y) because {
      if      (x == 0)     trivial
      else if (y == 0)     trivial
      else if (y % 2 == 0) {
        val z = y / 2
        check { fastExp(x, y)     == fastExp(x * x, z)                                   } &&
        check { fastExp(x * x, z) == exp(x * x, z)     because fastExpCorrect2(x * x, z) } &&
        check { exp(x * x, z)     == exp(x, y)         because square(x, z)              }
      }
      else                 {
        val z = (y - 1) / 2;
        check { fastExp(x, y)         == x * fastExp(x * x, z) because (y % 2 != 0)      } &&
        check { x * fastExp(x * x, z) == x * exp(x, y - 1)     because {
          check { fastExp(x * x, z)   == exp(x * x, z) because fastExpCorrect2(x * x, z) } &&
          check { exp(x * x, z)       == exp(x, 2 * z) because square(x, z)              } &&
          check { exp(x, 2 * z)       == exp(x, y - 1)                                   }
        }                                                                                } &&
        check { x * exp(x, y - 1)     == exp(x, y) because (y != 0) }
      }
    }
  }.holds

  /**
   * A more efficient function for computing exponentials.
   *
   * NOTE: this version of fastExp incorporates the correctness proof
   * directly into the post condition.  Leon is sometimes able to
   * verify the post-condition in seconds using Z3-F, but often times
   * out after >30s (Intel core i7, Ubuntu 14.04.2 LTS, x86-64,
   * 2015-06-04).
   */
  def fastExp2(x: BigInt, y: BigInt): BigInt = {
    require(y >= 0)
    if      (x == 0)     BigInt(0)
    else if (y == 0)     BigInt(1)
    else if (y % 2 == 0) fastExp2(x * x, y / 2)
    else                 x * fastExp2(x, y - 1)
  } ensuring { res =>
    res == exp(x, y) because {
      if      (x == 0)     trivial
      else if (y == 0)     trivial
      else if (y % 2 == 0) {
        val z = y / 2; {
          res                    ==| trivial                 |
          fastExp2(x * x, z)     ==| trivial /* ind. hyp. */ |
          exp(x * x, z)          ==| square(x, z)            |
          exp(x, y)
        }.qed
      }
      else                 {
        val z = (y - 1) / 2; {
          res                    ==| (y % 2 != 0)            |
          x * fastExp2(x * x, z) ==| {
            fastExp2(x * x, z)   ==| trivial /* ind. hyp. */ |
            exp(x * x, z)        ==| square(x, z)            |
            exp(x, 2 * z)        ==| trivial                 |
            exp(x, y - 1)                              }.qed |
          x * exp(x, y - 1)      ==| (y != 0)                |
          exp(x, y)
        }.qed
      }
    }
  }
}

